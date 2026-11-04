import ITree

namespace ITreeTests.Same

open CoFree

inductive PrintRandOp | print (x : Nat)
inductive PrintRandBr | rand

def PrintE : Effect := ⟨PrintRandOp, fun | .print _ => PUnit ⟩
def Rand : NonDeterminism := { Op := PrintRandBr, Resp | .rand => Nat }
abbrev PrintM (α : Type) := CoFree.{0, 0, 0} PrintE Rand α

def print (n : Nat) : PrintM Unit := perform (E := PrintE) (.print n)
def rand : PrintM Nat := branch (N := Rand) .rand

def print_rand : PrintM Unit := do print (← rand)

lemma print_rand_observe :
    ∃ k, print_rand.observe = .branch PrintRandBr.rand k ∧
    ∀ n : Nat, ∃ k', (k n).observe = .impure (PrintRandOp.print n) k' :=
  ⟨_, (observe_bind _ _).trans rfl, fun _ => ⟨_, (observe_bind _ _).trans rfl⟩⟩

theorem nondeterministic_unrelated_to_self : ∀ {Ret}, ¬Same Ret print_rand print_rand := by
  intro Ret h
  have ⟨k, hk, hkn⟩ := print_rand_observe
  have ⟨_, h0⟩ := hkn 0
  have ⟨_, h1⟩ := hkn 1
  have := Same.impure_inv (Same.branchR_inv (Same.branchL_inv h hk (0 : Nat)) hk (1 : Nat)) h0 h1
  cases this

theorem print_rand_nondeterministic : ¬Deterministic print_rand := nondeterministic_unrelated_to_self (Ret := Eq)

theorem print_rand_not_same_true : ¬Same (fun _ _ => True) print_rand print_rand :=
  nondeterministic_unrelated_to_self

theorem print_rand_not_same_any {Ret} {N} {m : CoFree.{0, 0, 0} PrintE N Unit} : ¬Same Ret print_rand m :=
  Same.not_of_not_self_left fun _ => nondeterministic_unrelated_to_self

/-- A branch whose responses print different numbers relates to neither output. -/
theorem print_rand_not_print_zero : ∀ {Ret}, ¬Same Ret print_rand (print 0) := by
  intro Ret h
  have ⟨k, hk, hkn⟩ := print_rand_observe
  have ⟨_, h1⟩ := hkn 1
  have := Same.impure_inv (Same.branchL_inv h hk (1 : Nat)) h1 rfl
  cases this

theorem rand_not_same_eq : ¬Deterministic rand :=
  fun h => nomatch Same.ret_inv
    (Same.branchR_inv (Same.branchL_inv h rfl (0 : Nat)) rfl (1 : Nat)) rfl rfl

def ignored_rand : PrintM Unit := do
  let _ ← rand
  print 5

lemma ignored_rand_observe : ∃ k, ignored_rand.observe = .branch PrintRandBr.rand k ∧
    ∀ r, (k r).observe = .impure (PrintRandOp.print 5) CoFree.pure :=
  ⟨_, (observe_bind _ _).trans rfl, fun _ => (observe_bind _ _).trans rfl⟩

theorem ignored_rand_deterministic : Deterministic ignored_rand :=
  let ⟨_, hb, hk⟩ := ignored_rand_observe
  (Same.branch_iff hb hb).mpr fun r₁ r₂ =>
    (Same.impure_iff (hk r₁) (hk r₂)).mpr fun _ => Same.ret rfl rfl rfl

theorem rand_not_same_eq_any {N : NonDeterminism} : ∀ m : CoFree.{0, 0, 0} PrintE N Nat, ¬Same Eq rand m :=
  fun _ h => rand_not_same_eq (Deterministic.of_same h).1

end ITreeTests.Same
