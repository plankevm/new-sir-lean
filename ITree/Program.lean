import ITree.Machine

/-! The program-writing surface over `CoFree` machines: `do` notation, loops, recursion, handlers. -/

universe u

namespace CoFree

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A : Type u}

instance : Monad (CoFree.{u} E N) where
  pure := CoFree.pure
  bind := CoFree.bind

/-- Runs silently forever. -/
def spin : CoFree E N A := ⟨PUnit, PEmpty, PUnit.unit, fun _ => .silent (.inl PUnit.unit), nofun⟩

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

instance : MonadLift (CoFree.{u} E N) (CoFree (E ⊕ₑ F) N) where
  monadLift t := mapOps (F := E ⊕ₑ F) Sum.inl (fun _ r => r) .id t

instance : MonadLift (CoFree.{u} F N) (CoFree (E ⊕ₑ F) N) where
  monadLift t := mapOps (F := E ⊕ₑ F) Sum.inr (fun _ r => r) .id t

end CoFree
