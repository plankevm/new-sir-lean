import ITree.Same
import Sir.Eval
import Sir.Ir

namespace Sir


def InitOutcomeEquiv : UB ⊕ InitOutcome → UB ⊕ InitOutcome → Prop
  | .inl _ub, _ => False
  | _, .inl _ub => False
  | .inr (.ret _ _ s₁), .inr (.ret _ _ s₂) => s₁ = s₂
  | o₁, o₂ => o₁ = o₂

def InitEquiv (p₁ p₂ : Program) : Prop :=
  ∀ l₁ l₂ e c w₀,
    CoFree.Same InitOutcomeEquiv
      (p₁.runInit l₁ c e w₀)
      (p₂.runInit l₂ c e w₀)

-- def Equiv (p₁ p₂ : Program) : Prop :=
--   InitEquiv 

end Sir
