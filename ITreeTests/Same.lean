import ITree

/-! `Same` on a small nondeterministic program: print a number the environment picks. -/

namespace ITreeTests.Same

open CoFree

inductive PrintRandOp | print (x : Nat)
inductive PrintRandBr | rand

def PrintRand : Effect where
  Op := PrintRandOp
  Resp | .print _ => PUnit
  BrOp := PrintRandBr
  BrResp | .rand => Nat

def print_rand : CoFree PrintRand Unit := do
  let res ← choose PrintRandBr.rand
  perform (PrintRandOp.print res)

theorem print_rand_observe :
    ∃ k, print_rand.observe = .branch PrintRandBr.rand k :=
  ⟨_, (observe_bind _ _).trans rfl⟩

theorem print_rand_observe2 :
    ∃ k, print_rand.observe = .branch PrintRandBr.rand k ∧
    ∀ n : Nat, ∃ k', (k n).observe = .impure (PrintRandOp.print n) k' :=
  ⟨_, (observe_bind _ _).trans rfl, fun _ => ⟨_, (observe_bind _ _).trans rfl⟩⟩

theorem nondet_unrelated_to_self : ∀ {Ret}, ¬Same Ret print_rand print_rand := by
  intro Ret ⟨rec, h₀, step⟩ 
  have same := step print_rand print_rand h₀
  have ⟨k, ⟨hk, hkn⟩⟩ := print_rand_observe2
  cases same with
  | ret a b h₁ _ _ => rw [hk] at h₁; cases h₁
  | impure op h₁ _ _ => rw [hk] at h₁; cases h₁
  | silentL h₁ _ => rw [hk] at h₁; cases h₁
  | silentR h₂ _ => rw [hk] at h₂; cases h₂
  | branchL op h₁ k_res =>
      rw [hk] at h₁
      have ⟨k₀, h0⟩ := hkn (0 : Nat)
      have ⟨k₁, h1⟩ := hkn (1 : Nat)
      cases h₁
      cases k_res (0 : Nat) with
      | ret _ _ _ e _ => rw [hk] at e; cases e
      | impure _ _ e _ => rw [hk] at e; cases e
      | silentL e _ => rw [h0] at e; cases e
      | silentR e _ => rw [hk] at e; cases e
      | branchL _ e _ => rw [h0] at e; cases e
      | branchR _ h₂ k_res₂ =>
          rw [hk] at h₂
          cases h₂
          cases k_res₂ (1 : Nat) with
          | ret _ _ e _ _ => rw [h0] at e; cases e
          | impure _ e0 e1 _ => rw [h0] at e0; rw [h1] at e1; cases e0; cases e1
          | silentL e _ => rw [h0] at e; cases e
          | silentR e _ => rw [h1] at e; cases e
          | branchL _ e _ => rw [h0] at e; cases e
          | branchR _ e _ => rw [h1] at e; cases e
          | mutualUnobservedStep e => simp [ForallUnobserved, h0] at e
      | mutualUnobservedStep e => simp [ForallUnobserved, h0] at e
  | branchR op h₂ k_res =>
      rw [hk] at h₂
      have ⟨k₀, h0⟩ := hkn (0 : Nat)
      have ⟨k₁, h1⟩ := hkn (1 : Nat)
      cases h₂
      cases k_res (1 : Nat) with
      | ret _ _ e _ _ => rw [hk] at e; cases e
      | impure _ e _ _ => rw [hk] at e; cases e
      | silentL e _ => rw [hk] at e; cases e
      | silentR e _ => rw [h1] at e; cases e
      | branchL _ h₁ k_res₁ =>
          rw [hk] at h₁
          cases h₁
          cases k_res₁ (0 : Nat) with
          | ret _ _ e _ _ => rw [h0] at e; cases e
          | impure _ e0 e1 _ => rw [h0] at e0; rw [h1] at e1; cases e0; cases e1
          | silentL e _ => rw [h0] at e; cases e
          | silentR e _ => rw [h1] at e; cases e
          | branchL _ e _ => rw [h0] at e; cases e
          | branchR _ e _ => rw [h1] at e; cases e
          | mutualUnobservedStep e => simp [ForallUnobserved, h0] at e
      | branchR _ e _ => rw [h1] at e; cases e
      | mutualUnobservedStep e => simp [ForallUnobserved, hk, h1] at e; cases e (0: Nat)
  | mutualUnobservedStep h =>
      simp [ForallUnobserved, hk] at h
      have ⟨k₀, h0⟩ := hkn 0
      have ⟨k₁, h1⟩ := hkn 1
      cases step _ _ (h (0 : Nat) (1 : Nat)) with
      | ret _ _ e _ _ => rw [h0] at e; cases e
      | impure op e₀ e₁ _ => rw [h0] at e₀; rw [h1] at e₁; cases e₀; cases e₁
      | silentL e _ => rw [h0] at e; cases e
      | silentR e _ => rw [h1] at e; cases e
      | branchL _ e _ => rw [h0] at e; cases e
      | branchR _ e _ => rw [h1] at e; cases e
      | mutualUnobservedStep e => simp [ForallUnobserved, h0] at e

/-- A branch whose responses print different numbers relates to neither output. -/
theorem print_rand_not_print_zero : ∀ {Ret}, ¬Same Ret print_rand (perform (PrintRandOp.print 0)) := by
  intro Ret h
  have ⟨k, hk, hkn⟩ := print_rand_observe2
  have ⟨_, h1⟩ := hkn 1
  have := Same.impure_inv (Same.branchL_inv h hk (1 : Nat)) h1 rfl
  cases this

end ITreeTests.Same
