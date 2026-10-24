import Sir.Same2
import Sir.Same

namespace Sir.Same2.Proofs

theorem isTau_of_forallUnobserved {t : Run} {p : Run → Prop}
    (h : CoFree.ForallUnobserved t p) : IsTau t := by
  unfold CoFree.ForallUnobserved at h
  split at h
  · rename_i h'; exact .silent h'
  · rename_i h'; exact .branch h'
  · exact h.elim

theorem forallUnobserved_tau {t t' : Run} {p : Run → Prop}
    (h : CoFree.ForallUnobserved t p) (ht : Tau t t') : p t' := by
  cases ht with
  | silent h' => exact (CoFree.forallUnobserved_silent h').mp h
  | branch r h' => exact (CoFree.forallUnobserved_branch h').mp h r

theorem same2F_of_sameFinite (R : Run → Run → Prop) {t₁ t₂ : Run}
    (h : CoFree.SameFinite Eq R t₁ t₂) : Same2F R t₁ t₂ := by
  induction h with
  | ret a => exact a.elim
  | impure op h₁ h₂ h => exact .visible op h₁ h₂ h
  | silentL h₁ _ ih =>
    refine .tauL (.silent h₁) fun t' ht => ?_
    cases ht with
    | silent h => rw [h₁] at h; cases h; exact ih
    | branch _ h => rw [h₁] at h; cases h
  | silentR h₂ _ ih =>
    refine .tauR (.silent h₂) fun t' ht => ?_
    cases ht with
    | silent h => rw [h₂] at h; cases h; exact ih
    | branch _ h => rw [h₂] at h; cases h
  | branchL _ h₁ _ ih =>
    refine .tauL (.branch h₁) fun t' ht => ?_
    cases ht with
    | silent h => rw [h₁] at h; cases h
    | branch r h => rw [h₁] at h; cases h; exact ih r
  | branchR _ h₂ _ ih =>
    refine .tauR (.branch h₂) fun t' ht => ?_
    cases ht with
    | silent h => rw [h₂] at h; cases h
    | branch r h => rw [h₂] at h; cases h; exact ih r
  | mutualUnobservedStep h =>
    obtain ⟨_, h', _⟩ := CoFree.forallUnobserved_exists h h
    exact .tau (isTau_of_forallUnobserved h) (isTau_of_forallUnobserved h')
      fun _ _ ht₁ ht₂ => forallUnobserved_tau (forallUnobserved_tau h ht₁) ht₂

/-- `Same2` still relates undefined behavior of different kinds (its `ub` rule), `Same` does
not, so only this direction holds. -/
theorem same2_of_same {t₁ t₂ : Run} : Same Eq t₁ t₂ → Same2 t₁ t₂
  | ⟨R, h, hR⟩ => ⟨R, fun _ _ h => same2F_of_sameFinite R (hR _ _ h), h⟩

end Sir.Same2.Proofs
