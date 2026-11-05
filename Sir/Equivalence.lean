import ITree.Same
import Sir.Eval
import Sir.Ir

namespace Sir

def DefinedAnd {α : Type} (r : α → α → Prop) : UB ⊕ α → UB ⊕ α → Prop
  | .inl _ub, _ => False
  | _, .inl _ub => False
  | .inr a, .inr b => r a b

def MainEquiv
  {p₁ p₂ : Program}
  (l₁ : Layout p₁)
  (l₂ : Layout p₂)
  (imms₁ : MainImmutablesMap p₁)
  (imms₂ : MainImmutablesMap p₂)
  : Prop :=
  ∀ static calldata e w₀,
    CoFree.Same (DefinedAnd Eq)
      (p₁.runMain l₁ imms₁ static calldata e w₀)
      (p₂.runMain l₂ imms₂ static calldata e w₀)

def DeployOutcomeEquiv {p₁ p₂ : Program} (l₁ : Layout p₁) (l₂ : Layout p₂)
  : InitOutcome → InitOutcome → Prop
  | .ret q₁ imms₁ s₁, .ret q₂ imms₂ s₂ =>
    s₁ = s₂ ∧ ∃ (h₁ : q₁ = p₁) (h₂ : q₂ = p₂), MainEquiv l₁ l₂ (h₁ ▸ imms₁) (h₂ ▸ imms₂)
  | o₁, o₂ => o₁ = o₂

def Equiv (p₁ p₂ : Program) : Prop :=
  Nonempty (Layout p₁) ∧ Nonempty (Layout p₂) ∧
  ∀ l₁ l₂ e c w₀,
    w₀.Unset e.address →
    CoFree.Same (DefinedAnd (DeployOutcomeEquiv l₁ l₂))
      (p₁.runInit l₁ c e w₀)
      (p₂.runInit l₂ c e w₀)

end Sir
