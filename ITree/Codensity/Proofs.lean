import ITree.Codensity

universe u

namespace CoFree.Cod.Proofs

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u}

theorem lawfulMonad : LawfulMonad (Cod.{u} E N) := LawfulMonad.mk' _
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)

theorem lower_pure (a : A) : (Pure.pure a : Cod E N A).lower = CoFree.pure a := rfl

end CoFree.Cod.Proofs
