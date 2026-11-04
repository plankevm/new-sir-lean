import ITree.Step

universe u v w w' s

inductive IterStep (S A : Type u) : Type u
  | «repeat» (s : S)
  | exit (a : A)

/-- A machine performing operations of `E` and branching on choices of `N`: its own states, plus
jumps that hand control to another machine for good. States live in `Type (max u v s)`, where
`s` is headroom: a machine whose states hold larger data (e.g. a machine of a lower universe)
can still return a small result. -/
structure CoFree (E : Effect.{u}) (N : NonDeterminism.{u}) (A : Type v) :
    Type (max (u+1) (v+1) (s+1)) where
  State : Type (max u v s)
  Jump : Type (max u v s)
  initial : State
  step : State → Step E N A (State ⊕ Jump)
  target : Jump → CoFree E N A

namespace CoFree

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A B : Type v}

def startAt (m : CoFree.{u, v, s} E N A) (s : m.State) : CoFree.{u, v, s} E N A :=
  { m with initial := s }

def next (m : CoFree.{u, v, s} E N A) : m.State ⊕ m.Jump → CoFree.{u, v, s} E N A
  | .inl s => m.startAt s
  | .inr j => m.target j

def observe (m : CoFree.{u, v, s} E N A) : Step E N A (CoFree.{u, v, s} E N A) :=
  (m.step m.initial).map m.next

/-! ## Positions

A position is a state of the machine or of any machine reachable through jumps. Combinators
whose own states must remember where a sub-machine is (loops, recursion, handlers) store
positions, because machines themselves are too large to be states. -/

def Pos : CoFree.{u, v, s} E N A → Type (max u v s)
  | ⟨S, _, _, _, target⟩ => S ⊕ (Σ j, Pos (target j))

def initPos : (m : CoFree.{u, v, s} E N A) → m.Pos
  | ⟨_, _, s₀, _, _⟩ => .inl s₀

def stepAt : (m : CoFree.{u, v, s} E N A) → m.Pos → Step E N A m.Pos
  | ⟨_, _, _, step, target⟩, .inl s => (step s).map fun
      | .inl s' => .inl s'
      | .inr j => .inr ⟨j, initPos (target j)⟩
  | ⟨_, _, _, _, target⟩, .inr ⟨j, p⟩ => (stepAt (target j) p).map fun p' => .inr ⟨j, p'⟩

def atPos : (m : CoFree.{u, v, s} E N A) → m.Pos → CoFree.{u, v, s} E N A
  | ⟨S, J, _, step, target⟩, .inl s => ⟨S, J, s, step, target⟩
  | ⟨_, _, _, _, target⟩, .inr ⟨j, p⟩ => atPos (target j) p

/-! ## Combinators -/

def pure (a : A) : CoFree.{u, v, s} E N A :=
  ⟨PUnit, PEmpty, ⟨⟩, fun _ => .pure a, nofun⟩

def silent (m : CoFree.{u, v, s} E N A) : CoFree.{u, v, s} E N A :=
  ⟨PUnit, PUnit, ⟨⟩, fun _ => .silent (.inr ⟨⟩), fun _ => m⟩

def tau : CoFree E .none PUnit := ⟨PUnit, PEmpty, ⟨⟩, fun _ => .silent (.inl ⟨⟩), nofun⟩


def perform (op : E.Op) : CoFree E N (E.Resp op) :=
  ⟨PUnit, E.Resp op, ⟨⟩, fun | .unit => .impure op .inr, pure⟩

def branch (c : N.Op) : CoFree E N (N.Resp c) :=
  ⟨PUnit, N.Resp c, ⟨⟩, fun _ => .branch c .inr, pure⟩

/-! ### Bind: the source's states, then a hand-off to the continuation -/

def bindTrans (g : A → CoFree.{u, v, s} E N B) {S J : Type (max u v s)} (step : S → Step E N A (S ⊕ J)) (s : S) :
    Step E N B (S ⊕ (J ⊕ (Σ a, (g a).State ⊕ (g a).Jump))) :=
  match step s with
  | .pure a => ((g a).step (g a).initial).map fun p => .inr (.inr ⟨a, p⟩)
  | .silent (.inl s) => .silent (.inl s)
  | .silent (.inr j) => .silent (.inr (.inl j))
  | .impure op k => .impure op fun r => match k r with
    | .inl s => .inl s
    | .inr j => .inr (.inl j)
  | .branch c k => .branch c fun r => match k r with
    | .inl s => .inl s
    | .inr j => .inr (.inl j)

def bind : CoFree.{u, v, s} E N A → (A → CoFree.{u, v, s} E N B) → CoFree.{u, v, s} E N B
  | ⟨S, J, s₀, step, target⟩, g =>
    { State := S
      Jump := J ⊕ (Σ a, (g a).State ⊕ (g a).Jump)
      initial := s₀
      step := bindTrans g step
      target
        | .inl j => bind (target j) g
        | .inr ⟨a, p⟩ => (g a).next p }

def bindStep (g : A → CoFree.{u, v, s} E N B) : Step E N A (CoFree.{u, v, s} E N A) → Step E N B (CoFree.{u, v, s} E N B)
  | .pure a => (g a).observe
  | .silent n => .silent (n.bind g)
  | .impure op k => .impure op fun r => (k r).bind g
  | .branch c k => .branch c fun r => (k r).bind g

def mapOps (e : Effect.Map E F) (nd : NonDeterminism.Map N M) : CoFree.{u, v, s} E N A →  CoFree.{u, v, s} F M A
  | ⟨State, Jump, initial, step, target⟩ => {
    State, Jump, initial,
    step := fun s => match step s with
      | .pure a => .pure a
      | .silent x => .silent x
      | .impure op k => .impure (e.op op) fun r => k (e.resp op r)
      | .branch c k => .branch (nd.op c) fun r => k (nd.resp c r)
    target j := mapOps e nd (target j)
  }

/-- The same machine with its result, and so its states, one universe up: lets a `do` block whose
mutable state is itself a machine call machines of the level below. -/
def up : CoFree.{u, v, s} E N A → CoFree.{u, max v w, s} E N (ULift.{w} A)
  | ⟨State, Jump, initial, step, target⟩ => {
    State := ULift.{w} State, Jump := ULift.{w} Jump, initial := ⟨initial⟩,
    step := fun s => match step s.down with
      | .pure a => .pure ⟨a⟩
      | .silent x => .silent (x.elim (.inl ⟨·⟩) (.inr ⟨·⟩))
      | .impure op k => .impure op fun r => (k r).elim (.inl ⟨·⟩) (.inr ⟨·⟩)
      | .branch c k => .branch c fun r => (k r).elim (.inl ⟨·⟩) (.inr ⟨·⟩)
    target j := up (target j.down)
  }

/-- Undoes `up`: the result comes back down, and the states keep theirs as headroom `s`. -/
def down : CoFree.{u, max v w, s} E N (ULift.{w} A) → CoFree.{u, v, max v w s} E N A
  | ⟨State, Jump, initial, step, target⟩ => {
    State, Jump, initial,
    step := fun st => match step st with
      | .pure a => .pure a.down
      | .silent x => .silent x
      | .impure op k => .impure op k
      | .branch c k => .branch c k
    target j := down (target j)
  }

/-! ### Loops -/

section Iter

variable {S : Type v}

/-- Runs `g s`; `.repeat s'` restarts at `g s'` after one silent step, `.exit a` returns `a`.
The state is the current index and a position in its body. -/
def iter (s : S) (g : S → CoFree.{u, v, s} E N (IterStep S A)) : CoFree.{u, v, s} E N A where
  State := Σ i, (g i).Pos
  Jump := PEmpty
  initial := ⟨s, (g s).initPos⟩
  step := fun ⟨i, p⟩ => match (g i).stepAt p with
    | .pure (.repeat i') => .silent (.inl ⟨i', (g i').initPos⟩)
    | .pure (.exit a) => .pure a
    | .silent p' => .silent (.inl ⟨i, p'⟩)
    | .impure op k => .impure op fun r => .inl ⟨i, k r⟩
    | .branch c k => .branch c fun r => .inl ⟨i, k r⟩
  target := nofun

end Iter

/-! ### Recursion -/

section Fix

variable {I O : Type u}

/-- The code a frame runs: the initial program, or the body at some input. -/
def fixCode (body : I → CoFree (Effect.Call I O ⊕ₑ E) N O) (t : CoFree (Effect.Call I O ⊕ₑ E) N O) :
    Option I → CoFree (Effect.Call I O ⊕ₑ E) N O
  | none => t
  | some i => body i

/-- A suspended caller: where to resume once the callee returns. -/
structure FixFrame (body : I → CoFree (Effect.Call I O ⊕ₑ E) N O)
    (t : CoFree (Effect.Call I O ⊕ₑ E) N O) : Type u where
  code : Option I
  resume : O → (fixCode body t code).Pos

structure FixState (body : I → CoFree (Effect.Call I O ⊕ₑ E) N O)
    (t : CoFree (Effect.Call I O ⊕ₑ E) N O) : Type u where
  code : Option I
  pos : (fixCode body t code).Pos
  stack : List (FixFrame body t)

/-- Runs `t`; a call `perform (.inl i)` pushes the caller and runs `body i`, and a return pops
it. Calls and returns each take one silent step. Branches pass through. -/
def fixFrom (body : I → CoFree (Effect.Call I O ⊕ₑ E) N O) (t : CoFree (Effect.Call I O ⊕ₑ E) N O) :
    CoFree E N O where
  State := FixState body t
  Jump := PEmpty
  initial := ⟨none, t.initPos, []⟩
  step := fun ⟨c, p, stack⟩ => match (fixCode body t c).stepAt p, stack with
    | .pure o, [] => .pure o
    | .pure o, ⟨c', k⟩ :: rest => .silent (.inl ⟨c', k o, rest⟩)
    | .silent p', stack => .silent (.inl ⟨c, p', stack⟩)
    | .impure (.inl i) k, stack => .silent (.inl ⟨some i, (body i).initPos, ⟨c, k⟩ :: stack⟩)
    | .impure (.inr op) k, stack => .impure op fun r => .inl ⟨c, k r, stack⟩
    | .branch b k, stack => .branch b fun r => .inl ⟨c, k r, stack⟩
  target := nofun

end Fix

end CoFree
