import ITree.Step

universe u w w'

inductive IterStep (S A : Type u) : Type u
  | «repeat» (s : S)
  | exit (a : A)

/-- A machine performing operations of `E` and branching on choices of `N`: its own states, plus
jumps that hand control to another machine for good. -/
structure CoFree (E : Effect.{u}) (N : NonDeterminism.{u}) (A : Type u) : Type (u+1) where
  State : Type u
  Jump : Type u
  initial : State
  step : State → Step E N A (State ⊕ Jump)
  target : Jump → CoFree E N A

namespace CoFree

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A B : Type u}

def startAt (m : CoFree E N A) (s : m.State) : CoFree E N A :=
  { m with initial := s }

def next (m : CoFree E N A) : m.State ⊕ m.Jump → CoFree E N A
  | .inl s => m.startAt s
  | .inr j => m.target j

def observe (m : CoFree E N A) : Step E N A (CoFree E N A) :=
  (m.step m.initial).map m.next

/-! ## Positions

A position is a state of the machine or of any machine reachable through jumps. Combinators
whose own states must remember where a sub-machine is (loops, recursion, handlers) store
positions, because machines themselves are too large to be states. -/

def Pos : CoFree E N A → Type u
  | ⟨S, _, _, _, target⟩ => S ⊕ (Σ j, Pos (target j))

def initPos : (m : CoFree E N A) → m.Pos
  | ⟨_, _, s₀, _, _⟩ => .inl s₀

def stepAt : (m : CoFree E N A) → m.Pos → Step E N A m.Pos
  | ⟨_, _, _, step, target⟩, .inl s => (step s).map fun
      | .inl s' => .inl s'
      | .inr j => .inr ⟨j, initPos (target j)⟩
  | ⟨_, _, _, _, target⟩, .inr ⟨j, p⟩ => (stepAt (target j) p).map fun p' => .inr ⟨j, p'⟩

def atPos : (m : CoFree E N A) → m.Pos → CoFree E N A
  | ⟨S, J, _, step, target⟩, .inl s => ⟨S, J, s, step, target⟩
  | ⟨_, _, _, _, target⟩, .inr ⟨j, p⟩ => atPos (target j) p

/-! ## Combinators -/

def pure (a : A) : CoFree E N A :=
  ⟨PUnit, PEmpty, ⟨⟩, fun _ => .pure a, nofun⟩

def silent (m : CoFree E N A) : CoFree E N A :=
  ⟨PUnit, PUnit, ⟨⟩, fun _ => .silent (.inr ⟨⟩), fun _ => m⟩

def impure (op : E.Op) (k : E.Resp op → CoFree E N A) : CoFree E N A :=
  ⟨PUnit, E.Resp op, ⟨⟩, fun _ => .impure op .inr, k⟩

def branch (c : N.Op) (k : N.Resp c → CoFree E N A) : CoFree E N A :=
  ⟨PUnit, N.Resp c, ⟨⟩, fun _ => .branch c .inr, k⟩

def corec {S : Type u} (f : S → Step E N A S) (s : S) : CoFree E N A :=
  ⟨S, PEmpty, s, fun s => (f s).map .inl, nofun⟩

/-! ### Bind: the source's states, then a hand-off to the continuation -/

def bindTrans (g : A → CoFree E N B) {S J : Type u} (step : S → Step E N A (S ⊕ J)) (s : S) :
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

def bind : CoFree E N A → (A → CoFree E N B) → CoFree E N B
  | ⟨S, J, s₀, step, target⟩, g =>
    { State := S
      Jump := J ⊕ (Σ a, (g a).State ⊕ (g a).Jump)
      initial := s₀
      step := bindTrans g step
      target
        | .inl j => bind (target j) g
        | .inr ⟨a, p⟩ => (g a).next p }

def bindStep (g : A → CoFree E N B) : Step E N A (CoFree E N A) → Step E N B (CoFree E N B)
  | .pure a => (g a).observe
  | .silent n => .silent (n.bind g)
  | .impure op k => .impure op fun r => (k r).bind g
  | .branch c k => .branch c fun r => (k r).bind g

/-! ### Renaming operations and branches -/

def mapStep {X : Type w} (f : E.Op → F.Op) (g : (op : E.Op) → F.Resp (f op) → E.Resp op)
    (b : NonDeterminism.Map N M) : Step E N A X → Step F M A X
  | .pure a => .pure a
  | .silent x => .silent x
  | .impure op k => .impure (f op) fun r => k (g op r)
  | .branch c k => .branch (b.op c) fun r => k (b.resp c r)

def mapOps (f : E.Op → F.Op) (g : (op : E.Op) → F.Resp (f op) → E.Resp op)
    (b : NonDeterminism.Map N M) : CoFree E N A → CoFree F M A
  | ⟨S, J, s₀, step, target⟩ =>
    ⟨S, J, s₀, fun s => mapStep f g b (step s), fun j => mapOps f g b (target j)⟩

/-! ### Loops -/

section Iter

variable {S : Type u}

/-- Runs `g s`; `.repeat s'` restarts at `g s'` after one silent step, `.exit a` returns `a`.
The state is the current index and a position in its body. -/
def iter (s : S) (g : S → CoFree E N (IterStep S A)) : CoFree E N A where
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

/-! ### Handlers -/

section Interp

variable {σ : Type u}

/-- States of a handled machine whose source has state type `S` and jump type `J`: running
the source, or running the handler for `op` with the source's continuation `k` pending. -/
inductive InterpState (h : σ → (op : E.Op) → CoFree F M (σ × E.Resp op)) (S J : Type u) : Type u
  | source (s : σ) (x : S)
  | handler (op : E.Op) (k : E.Resp op → S ⊕ J) (s : σ) (p : (h s op).Pos)

/-- One step of the handler for `op` at position `p`. When it returns, the source resumes
after one silent step. The handler's own branches stay branches. -/
def interpHandle (h : σ → (op : E.Op) → CoFree F M (σ × E.Resp op)) {S J : Type u}
    (op : E.Op) (k : E.Resp op → S ⊕ J) (s : σ) (p : (h s op).Pos) :
    Step F M (σ × A) (InterpState h S J ⊕ (σ × J)) :=
  match (h s op).stepAt p with
  | .pure (s', r) => .silent (match k r with
    | .inl x => .inl (.source s' x)
    | .inr j => .inr (s', j))
  | .silent p' => .silent (.inl (.handler op k s p'))
  | .impure op' k' => .impure op' fun r => .inl (.handler op k s (k' r))
  | .branch c k' => .branch c fun r => .inl (.handler op k s (k' r))

/-- The handled machine, started at `st`. Source jumps hand off to the handled jump target.
Source branches are not handled: they become branches of `M` through `b`. -/
def interpAt (h : σ → (op : E.Op) → CoFree F M (σ × E.Resp op)) (b : NonDeterminism.Map N M) :
    (m : CoFree E N A) → InterpState h m.State m.Jump → CoFree F M (σ × A)
  | ⟨S, J, _, step, target⟩, st =>
    { State := InterpState h S J
      Jump := σ × J
      initial := st
      step := fun
        | .source s x => match step x with
          | .pure a => .pure (s, a)
          | .silent (.inl x') => .silent (.inl (.source s x'))
          | .silent (.inr j) => .silent (.inr (s, j))
          | .impure op k => interpHandle h op k s (h s op).initPos
          | .branch c k => .branch (b.op c) fun r => match k (b.resp c r) with
            | .inl x' => .inl (.source s x')
            | .inr j => .inr (s, j)
        | .handler op k s p => interpHandle h op k s p
      target := fun (s, j) => interpAt h b (target j) (.source s (target j).initial) }

def interpState (h : σ → (op : E.Op) → CoFree F M (σ × E.Resp op)) (b : NonDeterminism.Map N M)
    (s : σ) (m : CoFree E N A) : CoFree F M (σ × A) :=
  interpAt h b m (.source s m.initial)

end Interp

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
