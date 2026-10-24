import Sir.Memory

/-! `Same` for SIR runs, written out in one place, without the generic `CoFree.Same`.

A run (`exec`, after `Mem` is handled) never returns: it ends with an operation that has no
answer (`stop`, `ret`, `revert`, `invalid`, `selfdestruct`, `fault`). So there is no return
relation, and only three things can happen next:

* a silent step (`Tau`): a `silent` node, or an allocation's branch, taken with any valid
  placement;
* a visible operation, any `HostOp`, which both runs must perform identically;
* undefined behavior (`fault (.ub _)`), which is terminal and relates to undefined behavior of
  any kind, and to nothing else.

`Same2 t₁ t₂` is the greatest relation that is closed under `Same2F`: finitely many silent steps
on one side (`tauL`, `tauR`, inductive), then one step of progress (`tau`, `visible`, `ub`).
Answers to silent steps are universally quantified on each side independently, so a run whose
behavior depends on where something was placed is not related even to itself.
`Sir.Same2.Proofs.same2_of_same` proves `Same Eq → Same2`. The converse fails: `CoFree.Same`
relates a fault only to the same fault, while `ub` here relates undefined behavior of any kind. -/

namespace Sir

abbrev Run := CoFree Exec Empty

/-- `t` takes a silent step to `t'`. -/
inductive Tau (t : Run) : Run → Prop
  | silent {t'} : t.observe = .silent t' → Tau t t'
  | branch {c k} (r : Choice.Resp c) : t.observe = .branch c k → Tau t (k r)

/-- `t` takes a silent step. A branch always has a placement to take (`Choice.placement` is made
only when one exists), so this needs no successor. -/
inductive IsTau (t : Run) : Prop
  | silent {t'} : t.observe = .silent t' → IsTau t
  | branch {c k} : t.observe = .branch c k → IsTau t

/-- One layer of `Same2`, with `R` for the pairs still to be checked. -/
inductive Same2F (R : Run → Run → Prop) : Run → Run → Prop
  | tau {t₁ t₂} : IsTau t₁ → IsTau t₂ → (∀ t₁' t₂', Tau t₁ t₁' → Tau t₂ t₂' → R t₁' t₂') →
      Same2F R t₁ t₂
  | tauL {t₁ t₂} : IsTau t₁ → (∀ t₁', Tau t₁ t₁' → Same2F R t₁' t₂) → Same2F R t₁ t₂
  | tauR {t₁ t₂} : IsTau t₂ → (∀ t₂', Tau t₂ t₂' → Same2F R t₁ t₂') → Same2F R t₁ t₂
  | visible {t₁ t₂} (op : HostOp) {k₁ k₂} : t₁.observe = .impure op k₁ →
      t₂.observe = .impure op k₂ → (∀ r, R (k₁ r) (k₂ r)) → Same2F R t₁ t₂
  | ub {t₁ t₂} (u₁ u₂ : UB) {k₁ k₂} : t₁.observe = .impure (.fault (.ub u₁)) k₁ →
      t₂.observe = .impure (.fault (.ub u₂)) k₂ → Same2F R t₁ t₂

def Same2 (t₁ t₂ : Run) : Prop :=
  ∃ R, (∀ t₁ t₂, R t₁ t₂ → Same2F R t₁ t₂) ∧ R t₁ t₂

end Sir
