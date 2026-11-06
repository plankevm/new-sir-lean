import Sir.Memory.Proofs

open Host

namespace Sir

theorem interp_memStep_taken_pairwise :
    ∀ (mem : MemState) (sir : SirM Empty) (m' : CoFree HostE MemoryND UB),
      mem.taken.Pairwise NatRange.Disjoint →
      CoFree.Reaches (CoFree.interp memStep mem sir) m' →
      ∃ (mem' : MemState) (sir' : SirM Empty),
        mem'.taken.Pairwise NatRange.Disjoint ∧ m' = CoFree.interp memStep mem' sir' :=
  Proofs.interp_memStep_taken_pairwise

theorem interpMem_taken_pairwise :
    ∀ (sir : SirM Empty) (m' : CoFree HostE MemoryND UB),
      CoFree.Reaches (interpMem sir) m' →
      m' = interpMem sir ∨ ∃ (mem : MemState) (sir' : SirM Empty),
        mem.taken.Pairwise NatRange.Disjoint ∧
          m'.observe = (CoFree.interp memStep mem sir').observe :=
  Proofs.interpMem_taken_pairwise

end Sir
