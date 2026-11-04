import ITreeTests.Same

/-! The monad laws up to `Same`, on a deterministic program built from a branch (`ignored_rand`),
so their determinism hypotheses are satisfiable; and on `print_rand`, where they fail. -/

namespace ITreeTests.SameLaws

open CoFree ITreeTests.Same

lemma print_deterministic (n : Nat) : Deterministic (print n) :=
  (Same.impure_iff rfl rfl).mpr fun _ => Same.ret rfl rfl rfl

theorem bind_deterministic : Deterministic (ignored_rand >>= fun _ => print 7) :=
  ignored_rand_deterministic.bind fun _ => print_deterministic 7

theorem pure_bind_ignored_rand : Same Eq (Pure.pure 3 >>= fun _ => ignored_rand) ignored_rand :=
  Deterministic.pure_bind ignored_rand_deterministic

theorem bind_pure_ignored_rand : Same Eq (ignored_rand >>= Pure.pure) ignored_rand :=
  ignored_rand_deterministic.bind_pure

theorem bind_assoc_ignored_rand :
    Same Eq (ignored_rand >>= (fun _ => ignored_rand) >>= fun _ => print 1)
      (ignored_rand >>= fun _ => ignored_rand >>= fun _ => print 1) :=
  ignored_rand_deterministic.bind_assoc (fun _ => ignored_rand_deterministic)
    fun _ => print_deterministic 1

/-- Without determinism the laws fail as equations: `print_rand >>= pure` is not even related to
`print_rand`. -/
theorem bind_pure_print_rand_fails : ¬Same Eq (print_rand >>= Pure.pure) print_rand :=
  fun h => print_rand_not_same_any (Deterministic.bind_pure_iff.mp h)

/-- Up to `Same` on one side, they still hold: both are related to nothing. -/
theorem bind_pure_print_rand_left {y : PrintM Unit} :
    Same Eq (print_rand >>= Pure.pure) y ↔ Same Eq print_rand y :=
  Same.bind_pure_left_iff

end ITreeTests.SameLaws
