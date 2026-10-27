import ITree.Codensity.Proofs

universe u

namespace CoFree.Cod

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u}

instance : LawfulMonad (Cod.{u} E N) :=
  Proofs.lawfulMonad

theorem lower_pure (a : A) : (Pure.pure a : Cod E N A).lower = CoFree.pure a :=
  Proofs.lower_pure a

end CoFree.Cod
