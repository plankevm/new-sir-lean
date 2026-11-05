import SirTests.Safety.Defs
import SirTests.Safety.Proofs

namespace SirTests.Safety

open Sir Host CoFree

theorem noop_safe : Safe noop := by
  intro l env imm hmode
  rcases env with ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, ⟨cd⟩ | _⟩
  · cases imm
    have hh := noop_init_halts l cd (Env.mk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (.creation cd))
    refine ⟨hh.runSafe, fun mainCode ho => ?_⟩
    cases hh.outcome Empty.elim ho
    refine ⟨⟨#v[], .empty, nofun⟩, ByteArray.append_empty, noop_mainSafe l _⟩
  · cases hmode

theorem initStops_not_safe : ¬Safe initStops := by
  intro hs
  obtain ⟨_, hmain⟩ := hs stopsLayout stopsEnv .init rfl
  obtain ⟨imms, heq, _⟩ := hmain .empty initStops_halts
  exact stopsLayout_withSetImmutables_ne imms heq

end SirTests.Safety
