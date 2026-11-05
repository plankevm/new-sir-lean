import SirTests.Safety.Defs
import SirTests.Safety.Proofs

namespace SirTests.Safety

open Sir Host CoFree

theorem noop_safe : Safe noop := by
  refine ⟨⟨noopLayout⟩, ?_⟩
  intro l env cd w₀ _
  have h := ((noop_init_halts l cd env).interpHost (self := env.address) ⟨w₀, .empty⟩).runInit
  have hm : l.toMainImmutables l.main = some ⟨#[], .empty⟩ :=
    (Layout.toMainImmutables_eq_some_iff _ _ _).2
      (by
        simp only [Layout.withSetImmutables, show (⟨#[], .empty⟩ : MainImmutables).WF noop by decide, ↓reduceDIte]
        exact congrArg some (congrArg (· ++ ByteArray.empty) (rfl : l.setImmutables #v[] = l.main) |>.trans
          ByteArray.append_empty))
  rw [hm] at h
  exact ⟨h.runSafe, fun imms _ ho => by
    cases h.outcome ho
    exact ⟨by decide, noop_mainSafe l _⟩⟩

theorem initStops_not_safe : ¬Safe initStops := by
  intro hs
  exact (hs.2 stopsLayout stopsEnv .empty stopsState stopsState_unset).1.2 ⟨_, initStops_halts⟩

end SirTests.Safety
