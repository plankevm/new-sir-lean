import ITree

namespace ITreeTests.Laws

open CoFree (perform silent iter fixFrom mapOps)
open CoFree (trace)
open Effect (Rec)

abbrev Ask : Effect := { Op := Nat, Resp _ := Nat }

abbrev Pick : NonDeterminism := { Op := Nat, Resp _ := Nat }

def ask (q : Nat) : CoFree Ask Pick Nat := perform (E := Ask) q

def pick (c : Nat) : CoFree Ask Pick Nat := CoFree.branch (N := Pick) c

def answers : List (Nat → Nat) :=
  [fun q => (q * 7 + 3) % 11, fun q => q, fun _ => 0, fun q => q * q % 13 + 1]

/-- Operations and branches are answered by the same function. -/
def observed {A : Type} (answer : Nat → Nat) (t : CoFree Ask Pick A) :
    Array (Option (Nat ⊕ Nat)) × Option A :=
  let (events, result) := trace answer answer 2000 t
  (events.map fun | .silent => none | .op q => some (.inl q) | .branch c => some (.inr c), result)

def same {A : Type} [BEq A] (name : String) (lhs rhs : CoFree Ask Pick A) : String × Bool :=
  (name, answers.all fun answer => observed answer lhs == observed answer rhs)

def programs : List (CoFree Ask Pick Nat) :=
  [ CoFree.pure 5,
    ask 3,
    silent (ask 2),
    (ask 3).bind fun x => if x > 5 then CoFree.pure x else silent (CoFree.pure (x + 1)),
    (ask 1).bind fun x => (ask (x + 1)).bind fun y => CoFree.pure (x + y),
    iter 0 fun i => (ask i).bind fun x =>
      CoFree.pure (if i < 4 then .repeat (i + 1) else .exit (x + i)),
    silent (pick 1),
    (pick 2).bind fun x => (ask x).bind fun y => CoFree.pure (x + y),
    iter 0 fun i => (pick i).bind fun x =>
      CoFree.pure (if i < 3 then .repeat (i + 1) else .exit (x + i)) ]

def conts : List (Nat → CoFree Ask Pick Nat) :=
  [ fun a => CoFree.pure (a + 1),
    fun a => (ask a).bind fun y => CoFree.pure (y + a),
    fun a => silent ((ask (a + 2)).bind fun y => silent (CoFree.pure y)),
    fun a => (pick a).bind fun y => CoFree.pure (y * 2) ]

def body : Nat → CoFree (Rec Nat Nat Ask) Pick Nat
  | 0 => CoFree.pure 1
  | i + 1 => (perform (E := Rec Nat Nat Ask) (.inl i)).bind fun r =>
    (perform (E := Rec Nat Nat Ask) (.inr (i + 1))).bind fun x => CoFree.pure (r + x)

def recPrograms : List (CoFree (Rec Nat Nat Ask) Pick Nat) :=
  [ CoFree.pure 3,
    body 3,
    silent (body 2),
    (perform (E := Rec Nat Nat Ask) (.inr 4)).bind fun x =>
      (perform (E := Rec Nat Nat Ask) (.inl (x % 3))).bind fun y => CoFree.pure (x + y),
    (CoFree.branch (E := Rec Nat Nat Ask) (N := Pick) 2).bind fun x =>
      (perform (E := Rec Nat Nat Ask) (.inl (x % 3))).bind fun y => CoFree.pure (x + y) ]

def monadLaws : List (String × Bool) :=
  (conts.map fun f => same "pure_bind" ((CoFree.pure 4).bind f) (f 4)) ++
  (programs.map fun t => same "bind_pure" (t.bind CoFree.pure) t) ++
  (programs.flatMap fun t => conts.flatMap fun f => conts.map fun g =>
    same "bind_assoc" ((t.bind f).bind g) (t.bind fun a => (f a).bind g)) ++
  (programs.flatMap fun t => conts.map fun f =>
    same "silent_bind" ((silent t).bind f) (silent (t.bind f)))

def loopBody (i : Nat) : CoFree Ask Pick (IterStep Nat Nat) :=
  (ask i).bind fun x => CoFree.pure (if x % 3 == 0 || i > 6 then .exit (x + i) else .repeat (i + 1))

def controlLaws : List (String × Bool) :=
  ([0, 1, 2].map fun s => same "iter_eq" (iter s loopBody)
    ((loopBody s).bind fun
      | .repeat s' => silent (iter s' loopBody)
      | .exit a => CoFree.pure a)) ++
  [same "fixFrom_pure" (fixFrom body (CoFree.pure 7)) (CoFree.pure 7)] ++
  (recPrograms.map fun t => same "fixFrom_silent" (fixFrom body (silent t))
    (silent (fixFrom body t))) ++
  ([0, 2, 3].map fun i => same "fixFrom_call"
    (fixFrom body ((perform (E := Rec Nat Nat Ask) (.inl i)).bind fun o => CoFree.pure (o + 1)))
    (silent ((fixFrom body (body i)).bind fun o => silent (fixFrom body (CoFree.pure (o + 1)))))) ++
  [same "fixFrom_op"
    (fixFrom body ((perform (E := Rec Nat Nat Ask) (.inr 5)).bind fun x => body (x % 3)))
    ((perform (E := Ask) 5).bind fun x => fixFrom body (body (x % 3)))] ++
  [same "fixFrom_br"
    (fixFrom body ((CoFree.branch (E := Rec Nat Nat Ask) (N := Pick) 5).bind fun x => body (x % 3)))
    ((pick 5).bind fun x => fixFrom body (body (x % 3)))]

def rename : Ask.Op → Ask.Op := (· + 100)

def handlerLaws : List (String × Bool) :=
  (programs.flatMap fun t => conts.map fun f => same "mapOps_bind"
    (mapOps (F := Ask) (M := Pick) rename (fun _ r => r) .id (t.bind f))
    ((mapOps (F := Ask) (M := Pick) rename (fun _ r => r) .id t).bind fun a =>
      mapOps (F := Ask) rename (fun _ r => r) .id (f a))) ++
  [same "mapOps_perform" (mapOps (F := Ask) (M := Pick) rename (fun _ r => r) .id (ask 4))
    ((ask 104).bind CoFree.pure)] ++
  [same "mapOps_choose" (mapOps (F := Ask) (M := Pick) rename (fun _ r => r) .id (pick 4))
    ((pick 4).bind CoFree.pure)]

def codensityLaws : List (String × Bool) :=
  (programs.map fun t => same "lower_lift" (CoFree.Cod.lift t).lower t) ++
  (programs.flatMap fun t => conts.map fun f => same "lower_bind"
    (CoFree.Cod.lift t >>= fun a => CoFree.Cod.lift (f a)).lower (t.bind f))

def checks : List (String × Bool) := monadLaws ++ controlLaws ++ handlerLaws ++ codensityLaws

#eval show IO Unit from do
  let failed := checks.filter (!·.2)
  unless failed.isEmpty do
    throw (IO.userError s!"law checks failed: {failed.map (·.1)}")
  IO.println s!"{checks.length} runtime law checks passed"

end ITreeTests.Laws
