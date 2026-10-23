import Sir.Same2
import Sir.Same

namespace Sir.Same2.Proofs

open CoFree (Next Silent)

theorem isUB_iff {op : HostOp} : op.isUB = true ↔ ∃ u, op = .fault (.ub u) := by
  cases op <;> simp [HostOp.isUB]
  rename_i f; cases f <;> simp

theorem next_iff_tau {t t' : Run} : Next t t' ↔ Tau t t' := by
  constructor
  · rintro (h | ⟨_, _, hk, r, rfl⟩)
    · exact .silent h
    · exact .br r hk
  · rintro (h | ⟨r, hk⟩)
    · exact .inl h
    · exact .inr ⟨_, _, hk, r, rfl⟩

theorem silent_iff {t : Run} : Silent t ↔ IsTau t := by
  constructor
  · rintro (⟨_, h⟩ | ⟨_, _, h⟩)
    · exact .silent h
    · exact .br h
  · rintro (h | h)
    · exact CoFree.silent_of_silent h
    · exact CoFree.silent_of_br h

theorem sameF_iff (R : Run → Run → Prop) {t₁ t₂ : Run} :
    CoFree.SameF Undefined Eq R t₁ t₂ ↔ Same2F R t₁ t₂ := by
  constructor
  · intro h
    induction h with
    | silent hs₁ hs₂ h =>
      exact .tau (silent_iff.mp hs₁) (silent_iff.mp hs₂)
        fun _ _ h₁ h₂ => h _ _ (next_iff_tau.mpr h₁) (next_iff_tau.mpr h₂)
    | impure op h₁ h₂ h =>
      exact .visible op h₁ h₂ h
    | @ret _ _ a => exact a.elim
    | ub op₁ op₂ h₁ h₂ hu₁ hu₂ =>
      obtain ⟨u₁, rfl⟩ := isUB_iff.mp hu₁
      obtain ⟨u₂, rfl⟩ := isUB_iff.mp hu₂
      exact .ub u₁ u₂ h₁ h₂
    | silentL hs _ ih => exact .tauL (silent_iff.mp hs) fun _ hn => ih _ (next_iff_tau.mpr hn)
    | silentR hs _ ih => exact .tauR (silent_iff.mp hs) fun _ hn => ih _ (next_iff_tau.mpr hn)
  · intro h
    induction h with
    | tau hs₁ hs₂ h =>
      exact .silent (silent_iff.mpr hs₁) (silent_iff.mpr hs₂)
        fun _ _ h₁ h₂ => h _ _ (next_iff_tau.mp h₁) (next_iff_tau.mp h₂)
    | visible op h₁ h₂ h => exact .impure op h₁ h₂ h
    | ub u₁ u₂ h₁ h₂ =>
      exact .ub _ _ h₁ h₂ rfl rfl
    | tauL hs _ ih => exact .silentL (silent_iff.mpr hs) fun _ hn => ih _ (next_iff_tau.mp hn)
    | tauR hs _ ih => exact .silentR (silent_iff.mpr hs) fun _ hn => ih _ (next_iff_tau.mp hn)

theorem same2_iff_same {t₁ t₂ : Run} : Same2 t₁ t₂ ↔ Same Eq t₁ t₂ :=
  ⟨fun ⟨R, hR, h⟩ => ⟨R, fun _ _ h => (sameF_iff R).mpr (hR _ _ h), h⟩,
   fun ⟨R, hR, h⟩ => ⟨R, fun _ _ h => (sameF_iff R).mp (hR _ _ h), h⟩⟩

end Sir.Same2.Proofs
