import ITree

/-! `Same` on a small nondeterministic program: print a number the environment picks. -/

namespace ITreeTests.Same

open CoFree

inductive PrintRandOp | print (x : Nat)
inductive PrintRandBr | rand

def PrintRand : Effect where
  Op := PrintRandOp
  Resp | .print _ => PUnit

def Rand : NonDeterminism where
  Op := PrintRandBr
  Resp | .rand => Nat
  resp_nonempty | .rand => ⟨(0 : Nat)⟩

def print_rand : CoFree PrintRand Rand Unit := do
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
theorem print_rand_not_print_zero : ∀ {Ret}, ¬Same Ret print_rand (perform (N := Rand) (PrintRandOp.print 0)) := by
  intro Ret h
  have ⟨k, hk, hkn⟩ := print_rand_observe2
  have ⟨_, h1⟩ := hkn 1
  have := Same.impure_inv (Same.branchL_inv h hk (1 : Nat)) h1 rfl
  cases this

/-! Weak `Ret`: determinism is only up to `Ret ∘ Ret⁻¹`. -/

/-- Returns a number the environment picks, with no visible operation. -/
def rand_nat : CoFree PrintRand Rand Nat := choose PrintRandBr.rand

/-- With a vacuous `Ret` the result's dependence on the branch is invisible. -/
theorem rand_nat_same_true : Same (fun _ _ => True) rand_nat rand_nat :=
  Same.branch rfl rfl fun _ _ => Same.ret rfl rfl trivial

theorem rand_nat_not_same_eq : ¬Same Eq rand_nat rand_nat := fun h =>
  nomatch Same.ret_inv
    (Same.branchR_inv (Same.branchL_inv h rfl (0 : Nat)) rfl (1 : Nat)) rfl rfl

/-- So `rand_nat` is `Eq`-related to nothing, though `True`-related to itself. -/
theorem rand_nat_not_same_eq_any {N : NonDeterminism} {m : CoFree PrintRand N Nat} : ¬Same Eq rand_nat m :=
  fun h => rand_nat_not_same_eq (Deterministic.of_same h).1

/-- A visible difference is not hidden by a vacuous `Ret`. -/
theorem print_rand_not_same_true : ¬Same (fun _ _ => True) print_rand print_rand :=
  nondet_unrelated_to_self

theorem print_rand_not_same_any {Ret : Unit → Unit → Prop} {N : NonDeterminism} {m : CoFree PrintRand N Unit} :
    ¬Same Ret print_rand m :=
  Same.not_of_not_self_left fun _ => nondet_unrelated_to_self

/-! Nondeterminism is not observed: the two sides may branch on different choices, or not at all. -/

/-- Prints `n` whichever number the environment picks. -/
def rand_then_print (n : Nat) : CoFree PrintRand Rand Unit :=
  CoFree.branch PrintRandBr.rand fun _ => perform (PrintRandOp.print n)

def print_det (n : Nat) : CoFree PrintRand .none Unit := perform (PrintRandOp.print n)

theorem rand_then_print_same_det (n : Nat) : Same Eq (rand_then_print n) (print_det n) :=
  Same.branch_const.mpr (Same.impure_iff.mpr fun _ => Same.ret rfl rfl rfl)

theorem det_same_rand_then_print (n : Nat) : Same Eq (print_det n) (rand_then_print n) :=
  Same.symm_eq (rand_then_print_same_det n)

theorem rand_then_print_ne (n m : Nat) (h : n ≠ m) : ¬Same Eq (rand_then_print n) (print_det m) :=
  fun hs => Same.impure_ne (fun e => h (by cases e; rfl)) (Same.branch_const.mp hs)

end ITreeTests.Same
