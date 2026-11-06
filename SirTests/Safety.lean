import SirTests.Safety.Defs
import SirTests.Safety.Proofs

namespace SirTests.Safety

open Sir Host CoFree

theorem noop_safe : Safe noop := by
  refine ⟨⟨⟨noopLayout⟩, ⟨noopLayout⟩, fun l₁ l₂ e cd w₀ _ => ?_⟩, fun l e cd w₀ _ => ?_⟩
  · refine (noop_init_returns l₁ cd e w₀).same (noop_init_returns l₂ cd e w₀) ⟨rfl, fun st cd' e' w => ?_⟩
    exact (noop_main_returns l₁ _ st cd' e' w).same (noop_main_returns l₂ _ st cd' e' w) rfl
  · have h := noop_init_returns l cd e w₀
    exact ⟨h.deterministic, fun imms _ ho => by
      cases h.outcome ho
      exact ⟨by decide, noop_mainSafe l _⟩⟩

theorem initStops_not_safe : ¬Safe initStops := fun hs =>
  Returns.same_inv (hs.1.2.2 stopsLayout stopsLayout stopsEnv .empty stopsState stopsState_unset)
    initStops_returns initStops_returns

end SirTests.Safety
