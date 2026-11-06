import Sir.Passes
import Sir.Passes.RemoveNoops.Proofs

namespace Sir

theorem Program.removeNoops_sound : TotalPassSound removeNoops :=
  fun _ hwf hs => ⟨Proofs.RemoveNoops.removeNoops_equiv hs,
    Proofs.RemoveNoops.removeNoops_safe hs, Proofs.RemoveNoops.removeNoops_wf hwf⟩

end Sir
