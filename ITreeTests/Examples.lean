import ITree

namespace ITreeTests.Examples

open CoFree (perform iter fix)
open CoFree (trace run)
open Effect (Rec)

inductive LogOp
  | emit (n : Nat)
  deriving BEq, Repr

abbrev Log : Effect := { Op := LogOp, Resp := fun | .emit _ => Unit }

def emit (n : Nat) := perform (E := Log) (N := .none) (.emit n)

def fib (n : Nat) : CoFree Log .none Nat :=
  iter (0, 1, 0) fun ((a, b, i) : Nat × Nat × Nat) => do
    emit a
    pure (if i < n then .repeat (b, a + b, i + 1) else .exit a)

def fib' (n : Nat) : CoFree Log .none Nat := do
  let mut (a, b, i) := (0, 1, 0)
  while i < n do
    emit a
    (a, b) := (b, a + b)
    i := i + 1
  return a

def countTo (n : Nat) : CoFree Log .none Nat := do
  let mut i := 0
  while i < n do
    emit i
    i := i + 1
  return i

def fact : Nat → CoFree Log .none Nat :=
  fix fun fact n => match n with
    | 0 => pure 1
    | n + 1 => do
      let r ← fact n
      perform (E := Rec Nat Nat Log) (.inr (.emit r))
      pure ((n + 1) * r)

/-- A level-1 program whose loop state is a level-0 tree: it re-emits every effect. -/
def replay (t : CoFree.{0} Log .none Nat) :
    CoFree.{1} (Effect.lift.{0, 1} Log) .none (ULift.{1} Nat) :=
  iter t fun t => match t.observe with
    | .pure n => pure (.exit ⟨n⟩)
    | .silent t' => pure (.repeat t')
    | .impure op k => (perform (E := Effect.lift.{0, 1} Log) ⟨op⟩).bind fun r =>
      pure (.repeat (k r.down))
    | .branch c _ => nomatch c

def emitted {A : Type} (t : CoFree Log .none A) : Array Nat × Option A :=
  let (events, result) := trace (E := Log) (N := .none) (fun _ => ()) nofun 10000 t
  (events.filterMap fun | .op (.emit n) => some n | _ => none, result)

def silents {E : Effect.{0}} {N : NonDeterminism.{0}} {A : Type} (answer : (op : E.Op) → E.Resp op)
    (pick : (c : N.Op) → N.Resp c) (t : CoFree E N A) : Nat :=
  ((trace answer pick 10000 t).1.filter fun | .silent => true | _ => false).size

def checks : List (String × Bool) :=
  [ ("fib 10", emitted (fib 10) == (#[0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55], some 55)),
    ("fib' 10", emitted (fib' 10) == (#[0, 1, 1, 2, 3, 5, 8, 13, 21, 34], some 55)),
    ("countTo 4", emitted (countTo 4) == (#[0, 1, 2, 3], some 4)),
    ("fact 5", emitted (fact 5) == (#[1, 1, 2, 6, 24], some 120)),
    ("replay fib 10",
      (run (E := Effect.lift.{0, 1} Log) (N := .none) (fun _ => ⟨()⟩) nofun 10000
        (replay (fib 10))).map ULift.down
        == some 55) ]

#eval show IO Unit from do
  let failed := checks.filter (!·.2)
  unless failed.isEmpty do
    throw (IO.userError s!"example checks failed: {failed.map (·.1)}")
  IO.println s!"{checks.length} example checks passed"

end ITreeTests.Examples
