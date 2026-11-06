import ITree.Same
import Sir.Eval
import Sir.Ir

namespace Sir

def MainEquiv
  {p₁ p₂ : Program}
  (l₁ : Layout p₁)
  (l₂ : Layout p₂)
  (imms₁ imms₂ : MainImmutables)
  : Prop :=
  ∀ static cd e w₀,
    CoFree.Same (DefinedAnd Eq)
      (p₁.runMain l₁ imms₁ static cd e w₀)
      (p₂.runMain l₂ imms₂ static cd e w₀)

def DeployOutcomeEquiv {p₁ p₂ : Program} (l₁ : Layout p₁) (l₂ : Layout p₂)
  : InitOutcome → InitOutcome → Prop
  | .ret imms₁ s₁, .ret imms₂ s₂ => s₁ = s₂ ∧ MainEquiv l₁ l₂ imms₁ imms₂
  | o₁, o₂ => o₁ = o₂

def Equiv (p₁ p₂ : Program) : Prop :=
  Nonempty (Layout p₁) ∧ Nonempty (Layout p₂) ∧
  ∀ l₁ l₂ e c w₀,
    w₀.Unset e.address →
    CoFree.Same (DefinedAnd (DeployOutcomeEquiv l₁ l₂))
      (p₁.runInit l₁ c e w₀)
      (p₂.runInit l₂ c e w₀)

end Sir
