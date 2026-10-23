import ITree.Machine

/-! The program-writing surface over `CoFree` machines: `do` notation, loops, recursion, handlers. -/

universe u

namespace CoFree

variable {E F : Effect.{u}} {A : Type u}

instance : Monad (CoFree.{u} E) where
  pure := CoFree.pure
  bind := CoFree.bind

def perform (op : E.Op) : CoFree E (E.Resp op) :=
  impure op pure

def choose (c : E.BrOp) : CoFree E (E.BrResp c) :=
  br c pure

def roll : Step E A (CoFree E A) → CoFree E A
  | .pure a => pure a
  | .silent m => silent m
  | .impure op k => impure op k
  | .br c k => br c k

instance : ForIn (CoFree.{u} E) Lean.Loop Unit where
  forIn _ init f := iter init fun b => (f ⟨⟩ b).bind fun
    | .yield b => pure (.repeat b)
    | .done b => pure (.exit b)

/-- Open recursion: `f call i` computes the result at `i`, where `call j` is a recursive call.
Runs on `fixFrom` with `call j := perform (.inl j)`. -/
def fix {I O : Type u} (f : (I → CoFree (Effect.Rec I O E) O) → I → CoFree (Effect.Rec I O E) O)
    (i : I) : CoFree E O :=
  let body := f fun j => perform (E := Effect.Rec I O E) (.inl j)
  fixFrom body (body i)

/-- Handles every operation of `E` with a program in `F`. Each handled operation is followed
by one silent step. Branches of `E` become branches of `F` through `b`. -/
def interp (h : (op : E.Op) → CoFree F (E.Resp op)) (b : Effect.BrMap E F) (t : CoFree E A) :
    CoFree F A :=
  (interpState (fun (_ : PUnit) op => (h op).bind fun r => pure (⟨⟩, r)) b ⟨⟩ t).bind
    fun v => pure v.2

instance : MonadLift (CoFree.{u} E) (CoFree (E ⊕ₑ F)) where
  monadLift t := mapOps (F := E ⊕ₑ F) Sum.inl (fun _ r => r) .inl t

instance : MonadLift (CoFree.{u} F) (CoFree (E ⊕ₑ F)) where
  monadLift t := mapOps (F := E ⊕ₑ F) Sum.inr (fun _ r => r) .inr t

end CoFree
