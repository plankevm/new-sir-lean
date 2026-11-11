import Sir.Passes
import Sir.Equivalence.Theorems

namespace Sir

theorem sound_of_composed_sound :
    ∀ f₁ f₂ : TotalPass, TotalPassSound f₁ → TotalPassSound f₂ → TotalPassSound (f₁ ∘ f₂) := by
  intro f₁ f₂ hs₁ hs₂ p hwf hsafe
  have ⟨hequiv', ⟨hsafe', hwf'⟩⟩ := hs₂ p hwf hsafe
  have ⟨hequiv'', h''⟩ := hs₁ (f₂ p) hwf' hsafe'
  constructor
  exact Equiv.trans hequiv' hequiv''
  exact h''

end Sir
