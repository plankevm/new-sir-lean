import SirTests.Safety.Defs
import SirTests.Safety.Proofs

namespace SirTests.Safety

open Sir Host CoFree

theorem noop_safe : Safe noop := by
  intro l env cd imm w₀ _
  cases imm
  have hh := (noop_init_halts l cd env).interpHost (self := env.address) ⟨w₀, .empty⟩
  refine ⟨hh.runSafe, fun mainCode w' ho => ?_⟩
  cases hh.outcome ho
  refine ⟨⟨#v[], .empty, nofun⟩, ByteArray.append_empty, noop_mainSafe l _⟩

theorem initStops_not_safe : ¬Safe initStops := by
  intro hs
  obtain ⟨_, hmain⟩ := hs stopsLayout stopsEnv .empty .init stopsState stopsState_unset
  obtain ⟨imms, heq, _⟩ := hmain .empty _ initStops_halts
  exact stopsLayout_withSetImmutables_ne imms heq

end SirTests.Safety
