import SirTests.Safety.Defs
import SirTests.Safety.Proofs

namespace SirTests.Safety

open Sir Host CoFree

theorem noop_safe : Safe noop := by
  intro l env cd w₀ _
  have h := ((noop_init_halts l cd env).interpHost (self := env.address) ⟨w₀, .empty⟩).runInit
  have hm : l.toMainImmutablesMap l.main = some ⟨#v[], .empty, nofun⟩ :=
    (Layout.toMainImmutablesMap_eq_some_iff _ _ _).2 ByteArray.append_empty
  rw [hm] at h
  exact ⟨h.runSafe, fun imms _ _ => noop_mainSafe l imms⟩

theorem initStops_not_safe : ¬Safe initStops := by
  intro hs
  exact (hs stopsLayout stopsEnv .empty stopsState stopsState_unset).1.2 ⟨_, initStops_halts⟩

end SirTests.Safety
