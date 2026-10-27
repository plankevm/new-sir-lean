import ITree.Machine

/-! The program-writing surface over `CoFree` machines: `do` notation, loops, recursion, handlers. -/

universe u

namespace CoFree

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A : Type u}

instance : Monad (CoFree.{u} E N) where
  pure := CoFree.pure
  bind := CoFree.bind

def perform (op : E.Op) : CoFree E N (E.Resp op) :=
  impure op pure

def choose (c : N.Op) : CoFree E N (N.Resp c) :=
  branch c pure

/-- Runs silently forever. -/
def spin : CoFree E N A := ⟨PUnit, PEmpty, PUnit.unit, fun _ => .silent (.inl PUnit.unit), nofun⟩

def roll : Step E N A (CoFree E N A) → CoFree E N A
  | .pure a => pure a
  | .silent m => silent m
  | .impure op k => impure op k
  | .branch c k => branch c k

instance : ForIn (CoFree.{u} E N) Lean.Loop Unit where
  forIn _ init f := iter init fun b => (f ⟨⟩ b).bind fun
    | .yield b => pure (.repeat b)
    | .done b => pure (.exit b)

/-- Open recursion: `f call i` computes the result at `i`, where `call j` is a recursive call.
Runs on `fixFrom` with `call j := perform (.inl j)`. -/
def fix {I O : Type u} (f : (I → CoFree (Effect.Rec I O E) N O) → I → CoFree (Effect.Rec I O E) N O)
    (i : I) : CoFree E N O :=
  let body := f fun j => perform (E := Effect.Rec I O E) (.inl j)
  fixFrom body (body i)

/-- Handles every operation of `E` with a program in `F`. Each handled operation is followed
by one silent step. Branches of `N` become branches of `M` through `b`. -/
def interp (h : (op : E.Op) → CoFree F M (E.Resp op)) (b : NonDeterminism.Map N M) (t : CoFree E N A) :
    CoFree F M A :=
  (interpState (fun (_ : PUnit) op => (h op).bind fun r => pure (⟨⟩, r)) b ⟨⟩ t).bind
    fun v => pure v.2

instance : MonadLift (CoFree.{u} E N) (CoFree (E ⊕ₑ F) N) where
  monadLift t := mapOps (F := E ⊕ₑ F) Sum.inl (fun _ r => r) .id t

instance : MonadLift (CoFree.{u} F N) (CoFree (E ⊕ₑ F) N) where
  monadLift t := mapOps (F := E ⊕ₑ F) Sum.inr (fun _ r => r) .id t

end CoFree
