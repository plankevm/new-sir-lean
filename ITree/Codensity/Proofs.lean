import ITree.Codensity

universe u

namespace CoFree.Cod.Proofs

variable {E : Effect.{u}} {A : Type u}

theorem lawfulMonad : LawfulMonad (Cod.{u} E) := LawfulMonad.mk' _
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)

theorem lower_pure (a : A) : (Pure.pure a : Cod E A).lower = CoFree.pure a := rfl

end CoFree.Cod.Proofs
