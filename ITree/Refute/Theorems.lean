import ITree.Refute.Proofs

universe u

namespace CoFree

variable {E : Effect.{u}} {N₁ N₂ : NonDeterminism.{u}} {A B : Type u}

theorem Same.not_bad : ∀ {Ret : A → B → Prop} {x : CoFree E N₁ A} {y : CoFree E N₂ B},
    Bad Ret x y → ¬Same Ret x y :=
  Proofs.Same.not_bad

theorem Same.of_not_bad : ∀ {Ret : A → B → Prop} {x : CoFree E N₁ A} {y : CoFree E N₂ B},
    ¬Bad Ret x y → Same Ret x y :=
  Proofs.Same.of_not_bad

theorem Same.hasOutcome_left : ∀ {Ret : A → B → Prop} {x : CoFree E N₁ A} {y : CoFree E N₂ B} {b : B},
    Same Ret x y → HasOutcome y (.res b) → ∃ a, HasOutcome x (.res a) ∧ Ret a b :=
  fun h ho => Proofs.Same.hasOutcome_left h ho _ rfl

end CoFree
