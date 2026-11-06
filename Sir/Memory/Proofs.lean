import Sir.Memory
import ITree.Reaches.Theorems

open Host

namespace Sir.Proofs

lemma size_copySlice_zero (src dest : ByteArray) (off len : Nat) (h : off + len ≤ dest.size) :
    (src.copySlice 0 dest off len).size = dest.size := by
  simp only [ByteArray.copySlice, ByteArray.size, Array.size_append, Array.size_extract] at *
  omega

lemma taken_write (m : MemState) {offset : Word} {length : Nat} (bytes : ByteArray)
    (r : m.Region offset length) : (m.write bytes r).taken = m.taken := by
  obtain ⟨j, hle, hend⟩ := r
  simp only [MemState.taken, MemState.write, List.cons.injEq, true_and]
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, Array.getElem_toList, Array.getElem_modify]
  split
  · rename_i hij
    subst hij
    simp only [Allocation.range, Allocation.size, NatRange.mk.injEq, true_and]
    apply size_copySlice_zero
    simp only [Fin.getElem_fin, Allocation.end, Allocation.size] at hle hend
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hle)]
    omega
  · rfl

lemma pairwise_push (m : MemState) (a : Allocation) (size : Nat)
    (hI : m.taken.Pairwise NatRange.Disjoint) (hv : m.ValidAlloc size a) :
    (m.push a).taken.Pairwise NatRange.Disjoint := by
  have : (m.push a).taken = m.taken ++ [a.range] := by
    simp [MemState.taken, MemState.push]
  rw [this, List.pairwise_append]
  exact ⟨hI, List.pairwise_singleton _ _, fun r hr _ hb => (List.mem_singleton.1 hb) ▸ hv.2.2 r hr⟩

lemma validAlloc_zeroed (m : MemState) (size : Nat) (a : Allocation) (hv : m.ValidAlloc size a) :
    m.ValidAlloc size { a with bytes := ⟨.replicate a.size 0⟩ } := by
  have hs : Allocation.size { a with bytes := ⟨.replicate a.size 0⟩ } = a.size := by
    simp only [Allocation.size, ByteArray.size, Array.size_replicate]
  obtain ⟨hsz, hend, hd⟩ := hv
  refine ⟨hs.trans hsz, ?_, ?_⟩
  · simpa only [Allocation.end, hs] using hend
  · simpa only [Allocation.range, hs] using hd

lemma memStep_silent {X : Type} (mem : MemState) (s : Step EvalE .none Empty X) (x : MemState × X)
    (hI : mem.taken.Pairwise NatRange.Disjoint) (h : memStep mem s = .silent x) :
    x.1.taken.Pairwise NatRange.Disjoint := by
  unfold memStep at h
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with h; subst h; first | exact hI | (simp only [taken_write]; exact hI))

lemma memStep_impure {X : Type} (mem : MemState) (s : Step EvalE .none Empty X) op k r
    (hI : mem.taken.Pairwise NatRange.Disjoint) (h : memStep mem s = .impure op k) :
    (k r).1.taken.Pairwise NatRange.Disjoint := by
  unfold memStep at h
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with hop hk; subst hop; cases hk; exact hI)

lemma memStep_branch {X : Type} (mem : MemState) (s : Step EvalE .none Empty X) c k r
    (hI : mem.taken.Pairwise NatRange.Disjoint) (h : memStep mem s = .branch c k) :
    (k r).1.taken.Pairwise NatRange.Disjoint := by
  unfold memStep at h
  repeat' split at h
  all_goals try contradiction
  all_goals
    injection h with hc hk
    subst hc
    cases hk
    obtain ⟨a', hv⟩ := r
  · exact pairwise_push _ _ _ hI (validAlloc_zeroed _ _ _ hv)
  · exact hI
  · exact pairwise_push _ _ _ hI hv
  · exact hI

theorem interp_memStep_taken_pairwise (mem : MemState) (sir : SirM Empty)
    (m' : CoFree HostE MemoryND UB) (hI : mem.taken.Pairwise NatRange.Disjoint)
    (hr : CoFree.Reaches (CoFree.interp memStep mem sir) m') :
    ∃ (mem' : MemState) (sir' : SirM Empty), mem'.taken.Pairwise NatRange.Disjoint ∧
      m' = CoFree.interp memStep mem' sir' :=
  CoFree.interp_reaches memStep (fun m => m.taken.Pairwise NatRange.Disjoint)
    (fun st s x hI h => memStep_silent st s x hI h)
    (fun st s _ k r hI h => memStep_impure st s _ k r hI h)
    (fun st s _ k r hI h => memStep_branch st s _ k r hI h) mem sir m' hI hr

theorem interpMem_taken_pairwise (sir : SirM Empty) (m' : CoFree HostE MemoryND UB)
    (hr : CoFree.Reaches (interpMem sir) m') :
    m' = interpMem sir ∨ ∃ (mem : MemState) (sir' : SirM Empty),
      mem.taken.Pairwise NatRange.Disjoint ∧ m'.observe = (CoFree.interp memStep mem sir').observe := by
  have ho : (interpMem sir).observe = .branch (.pick (Word.size - CompilerReservedBytes) (by decide))
      fun start => (CoFree.pure start).bind fun start =>
        CoFree.interp memStep { live := #[], reserved := ⟨start.val, CompilerReservedBytes⟩ } sir :=
    CoFree.observe_bind _ _
  cases hr with
  | refl => exact .inl rfl
  | silent h _ => rw [ho] at h; cases h
  | impure _ h _ => rw [ho] at h; cases h
  | branch r h hr =>
    rw [ho] at h
    injection h with hc hk
    subst hc
    cases hk
    right
    have hI : ({ live := #[], reserved := ⟨r.val, CompilerReservedBytes⟩ } : MemState).taken.Pairwise
        NatRange.Disjoint := by simp [MemState.taken]
    rcases CoFree.reaches_of_observe_eq (CoFree.observe_bind _ _) hr with rfl | hr
    · exact ⟨_, sir, hI, CoFree.observe_bind _ _⟩
    · obtain ⟨mem, sir', hI', rfl⟩ := interp_memStep_taken_pairwise _ sir _ hI hr
      exact ⟨mem, sir', hI', rfl⟩

end Sir.Proofs
