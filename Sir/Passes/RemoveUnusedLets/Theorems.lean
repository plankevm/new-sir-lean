import Sir.Passes
import Sir.Passes.RemoveUnusedLets.Proofs

namespace Sir

theorem Program.removeUnusedLets_sound : TotalPassSound removeUnusedLets :=
  fun _ hwf hs => ⟨Proofs.RemoveUnusedLets.removeUnusedLets_equiv hs,
    Proofs.RemoveUnusedLets.removeUnusedLets_safe hs, Proofs.RemoveUnusedLets.removeUnusedLets_wf hwf⟩

end Sir
