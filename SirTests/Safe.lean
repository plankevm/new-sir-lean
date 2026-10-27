import SirTests.Same
import Sir
import Host.Outcome.Proofs

/-! `HasOutcome` and `Safe` on small programs (those of `SirTests.Same`). -/

namespace SirTests.Safe

open Sir Host CoFree SirTests.Same

theorem hasOutcome_skip_iff (n : Nat) {t : CoFree Exec SirND Empty} {o : Host.Outcome} :
    HasOutcome (skip n t) o ↔ HasOutcome t o := by
  induction n generalizing t with
  | zero => exact .rfl
  | succ n ih =>
    unfold skip
    split
    next t' ht => exact ih.trans (HasOutcome.silent_iff ht).symm
    next => exact .rfl

theorem stops_outcome {o : Host.Outcome} : HasOutcome (run stops) o ↔ o = .ret .empty default := by
  rw [← hasOutcome_skip_iff 100]
  exact HasOutcome.halt_iff (observe_of_headOp (op := stopOp default) (by kernel_rfl)) Empty.elim

/-- Storage is concrete: `sload` reads what the run itself stored. -/
theorem storeLoads_outcome {o : Host.Outcome} :
    HasOutcome (run storeLoads) o ↔ o = .ret .empty ⟨((default : Storage).set 0 5).set 1 5, default⟩ := by
  rw [← hasOutcome_skip_iff 100]
  exact HasOutcome.halt_iff
    (observe_of_headOp (op := .ret .empty ⟨((default : Storage).set 0 5).set 1 5, default⟩)
      (by kernel_rfl)) Empty.elim

theorem stops_safe : Safe (run stops) :=
  ⟨fun _ h => (nomatch stops_outcome.1 h), (Deterministic.of_same mallocs_same_stops).2⟩

/-- Safety carries over to related runs. -/
theorem mallocs_safe : Safe (run mallocs) :=
  stops_safe.of_same (Same.symm_eq mallocs_same_stops)

theorem mallocs_outcome {o : Host.Outcome} : HasOutcome (run mallocs) o ↔ o = .ret .empty default :=
  (Same.hasOutcome_iff mallocs_same_stops).trans stops_outcome

theorem switchUB_not_safe : ¬Safe (run switchUB) :=
  not_safe_of_hasOutcome_ub ((hasOutcome_skip_iff 100).1
    (.halt Empty.elim (observe_of_headOp (op := .ub .switchNoMatch) (by kernel_rfl))))

theorem undefinedVar_outcome {o : Host.Outcome} : HasOutcome (run undefinedVar) o ↔ o = .ub .malformed := by
  rw [← hasOutcome_skip_iff 100]
  exact HasOutcome.halt_iff (observe_of_headOp (op := .ub .malformed) (by kernel_rfl)) Empty.elim

/-- A malformed program is never `Safe`. -/
theorem undefinedVar_not_safe : ¬Safe (run undefinedVar) :=
  not_safe_of_hasOutcome_ub (undefinedVar_outcome.2 rfl)

theorem leaks_not_safe : ¬Safe (run leaks) :=
  fun h => leaks_not_deterministic h.2

/-! A run with no UB that is unsafe: which outcome it has depends on the placement. -/

def oneByte : Choice := .placement 1 [] ⟨0, by decide⟩

def placementDecides : CoFree Exec SirND Empty :=
  CoFree.branch oneByte fun r =>
    if r.1 = 0 then CoFree.impure (stopOp default) nofun else CoFree.impure .invalid nofun

theorem placementDecides_outcome {o : Host.Outcome} :
    HasOutcome placementDecides o ↔ o = .ret .empty default ∨ o = .invalid := by
  unfold placementDecides
  rw [HasOutcome.branch_iff (CoFree.observe_branch _ _)]
  constructor
  · rintro ⟨r, h⟩
    split at h
    · exact .inl ((HasOutcome.halt_iff (CoFree.observe_impure _ _) Empty.elim).1 h)
    · exact .inr ((HasOutcome.halt_iff (CoFree.observe_impure _ _) Empty.elim).1 h)
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by decide⟩, .halt Empty.elim (CoFree.observe_impure _ _)⟩
    · exact ⟨⟨1, by decide⟩, .halt Empty.elim (CoFree.observe_impure _ _)⟩

theorem placementDecides_no_ub {u : UB} : ¬HasOutcome placementDecides (.ub u) := by
  rw [placementDecides_outcome]; simp

theorem placementDecides_not_safe : ¬Safe placementDecides :=
  not_safe_of_branch_outcomes (c := oneByte) (r₁ := ⟨0, by decide⟩) (r₂ := ⟨1, by decide⟩)
    (CoFree.observe_branch _ _) (CoFree.observe_impure _ _) (CoFree.observe_impure _ _)
    Empty.elim Empty.elim nofun

end SirTests.Safe
