import Host.Outcome
import ITree.Same.Theorems

namespace Host

/-! ## Outcomes are the terminal operations -/

theorem Outcome.op_resp_empty (o : Outcome) (r : WorldOp.Resp o.op) : False := by
  cases o <;> exact nomatch r

theorem Outcome.op_injective {o₁ o₂ : Outcome} (h : o₁.op = o₂.op) : o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> simp_all [Outcome.op]

/-- Every operation without an answer ends a run with some outcome. -/
theorem Outcome.exists_op {op : WorldOp} (h : WorldOp.Resp op → False) :
    ∃ o : Outcome, o.op = op := by
  cases op
  case ret d st => exact ⟨.ret d st, rfl⟩
  case revert d => exact ⟨.revert d, rfl⟩
  case invalid => exact ⟨.invalid, rfl⟩
  case selfdestruct a st => exact ⟨.selfdestruct a st, rfl⟩
  case ub u => exact ⟨.ub u, rfl⟩
  case call k _ _ _ _ => cases k <;> exact (h (by unfold WorldOp.Resp; exact default)).elim
  all_goals exact (h (by unfold WorldOp.Resp; exact default)).elim

/-! ## One step -/

variable {t t' : CoFree WorldE Empty} {o o' : Outcome}

theorem HasOutcome.congr (h : HasOutcome t o) (he : t.observe = t'.observe) : HasOutcome t' o := by
  cases h with
  | halt hk => exact .halt (he ▸ hk)
  | silent hs h => exact .silent (he ▸ hs) h
  | branch r hb h => exact .branch r (he ▸ hb) h
  | impure r hi h => exact .impure r (he ▸ hi) h

/-- A run at its terminal operation has exactly that outcome. -/
theorem HasOutcome.halt_iff {k : WorldOp.Resp o.op → CoFree WorldE Empty}
    (hk : t.observe = .impure o.op k) : HasOutcome t o' ↔ o' = o := by
  constructor
  · intro h
    cases h with
    | halt h =>
      rw [hk] at h
      injection h with hop
      exact Outcome.op_injective (by first | exact hop | exact hop.symm)
    | silent h _ => rw [hk] at h; cases h
    | branch _ h _ => rw [hk] at h; cases h
    | impure r h _ => rw [hk] at h; cases h; exact (o.op_resp_empty r).elim
  · rintro rfl; exact .halt hk

theorem HasOutcome.silent_iff (hs : t.observe = .silent t') :
    HasOutcome t o ↔ HasOutcome t' o := by
  constructor
  · intro h
    cases h with
    | halt h => rw [hs] at h; cases h
    | silent h h' => rw [hs] at h; cases h; exact h'
    | branch _ h _ => rw [hs] at h; cases h
    | impure _ h _ => rw [hs] at h; cases h
  · exact .silent hs

theorem HasOutcome.branch_iff {c : Choice} {k : Choice.Resp c → CoFree WorldE Empty}
    (hb : t.observe = .branch c k) : HasOutcome t o ↔ ∃ r, HasOutcome (k r) o := by
  constructor
  · intro h
    cases h with
    | halt h => rw [hb] at h; cases h
    | silent h _ => rw [hb] at h; cases h
    | branch r h h' => rw [hb] at h; cases h; exact ⟨r, h'⟩
    | impure _ h _ => rw [hb] at h; cases h
  · rintro ⟨r, h⟩; exact .branch r hb h

/-- A host operation either ends the run with `o`, or some answer to it leads to `o`. -/
theorem HasOutcome.impure_iff {op : WorldOp} {k : WorldOp.Resp op → CoFree WorldE Empty}
    (hi : t.observe = .impure op k) :
    HasOutcome t o ↔ op = o.op ∨ ∃ r, HasOutcome (k r) o := by
  constructor
  · intro h
    cases h with
    | halt h => rw [hi] at h; cases h; exact .inl rfl
    | silent h _ => rw [hi] at h; cases h
    | branch _ h _ => rw [hi] at h; cases h
    | impure r h h' => rw [hi] at h; cases h; exact .inr ⟨r, h'⟩
  · rintro (rfl | ⟨r, h⟩)
    · exact .halt hi
    · exact .impure r hi h

/-- A terminal operation gives the run an outcome. -/
theorem HasOutcome.of_terminal {op : WorldOp} {k : WorldOp.Resp op → CoFree WorldE Empty}
    (hi : t.observe = .impure op k) (hop : WorldOp.Resp op → False) : ∃ o, HasOutcome t o := by
  obtain ⟨o, rfl⟩ := Outcome.exists_op hop
  exact ⟨o, .halt hi⟩

theorem not_hasOutcome_spin : ¬HasOutcome (CoFree.spin : CoFree WorldE Empty) o := by
  suffices ∀ t, HasOutcome t o → t = CoFree.spin → False from fun h => this _ h rfl
  intro t h
  induction h with
  | halt h => rintro rfl; rw [CoFree.spin_observe] at h; cases h
  | silent h _ ih => rintro rfl; rw [CoFree.spin_observe] at h; cases h; exact ih rfl
  | branch _ h _ => rintro rfl; rw [CoFree.spin_observe] at h; cases h
  | impure _ h _ => rintro rfl; rw [CoFree.spin_observe] at h; cases h

/-! ## Related runs have the same outcomes -/

/-- `t₂` is related to a run performing `op`, so it reaches `op` after finitely many unobserved
steps, each taken with any one response. -/
private theorem hasOutcome_of_sameFinite_impure {Ret : Empty → Empty → Prop}
    {R : CoFree WorldE Empty → CoFree WorldE Empty → Prop} {t₁ t₂ : CoFree WorldE Empty}
    {op : WorldOp}
    {k₁ : WorldOp.Resp op → CoFree WorldE Empty} (h : CoFree.SameFinite Ret R t₁ t₂)
    (h₁ : t₁.observe = .impure op k₁)
    (H : ∀ n (k₂ : WorldOp.Resp op → CoFree WorldE Empty), n.observe = .impure op k₂ →
      (∀ r, R (k₁ r) (k₂ r)) → HasOutcome n o) : HasOutcome t₂ o := by
  induction h with
  | ret _ _ h => rw [h₁] at h; cases h
  | impure _ h hm₂ hrec => rw [h₁] at h; cases h; exact H _ _ hm₂ hrec
  | silentL h => rw [h₁] at h; cases h
  | silentR hm₂ _ ih => exact .silent hm₂ (ih h₁)
  | branchL _ h => rw [h₁] at h; cases h
  | branchR c hm₂ _ ih =>
    obtain ⟨r⟩ := WorldE.brResp_nonempty c
    exact .branch r hm₂ (ih r h₁)
  | mutualUnobservedStep h => exact (CoFree.not_forallUnobserved_impure h₁ h).elim

theorem HasOutcome.of_same {Ret : Empty → Empty → Prop} {t₁ t₂ : CoFree WorldE Empty}
    (h : CoFree.Same Ret t₁ t₂) (ho : HasOutcome t₁ o) : HasOutcome t₂ o := by
  induction ho generalizing t₂ with
  | halt hk =>
    exact hasOutcome_of_sameFinite_impure (CoFree.Same.unfold h) hk fun _ _ hn _ => .halt hn
  | silent hs _ ih => exact ih (CoFree.Same.silentL_inv h hs)
  | branch r hb _ ih => exact ih (CoFree.Same.branchL_inv h hb r)
  | impure r hi _ ih =>
    exact hasOutcome_of_sameFinite_impure (CoFree.Same.unfold h) hi fun _ _ hn hrec =>
      .impure r hn (ih (hrec r))

theorem Same.hasOutcome_iff {Ret : Empty → Empty → Prop} {t₁ t₂ : CoFree WorldE Empty}
    (h : CoFree.Same Ret t₁ t₂) : HasOutcome t₁ o ↔ HasOutcome t₂ o :=
  ⟨HasOutcome.of_same h, HasOutcome.of_same (CoFree.Same.symm h)⟩

/-- In a deterministic run, every response to a branch leads to the same outcomes. -/
theorem Deterministic.hasOutcome_branch {c : Choice} {k : Choice.Resp c → CoFree WorldE Empty}
    (h : CoFree.Deterministic t) (hb : t.observe = .branch c k) (r₁ r₂ : Choice.Resp c) :
    HasOutcome (k r₁) o ↔ HasOutcome (k r₂) o :=
  Same.hasOutcome_iff (CoFree.Same.branchR_inv (CoFree.Same.branchL_inv h hb r₁) hb r₂)

/-! ## Safety -/

/-- A run related to a safe run is safe: what a correct compiler emits for a safe program. -/
theorem Safe.of_same {t₁ t₂ : CoFree WorldE Empty} (h : Safe t₁) (hs : CoFree.Same Eq t₁ t₂) :
    Safe t₂ :=
  ⟨fun u hu => h.1 u ((Same.hasOutcome_iff hs).2 hu), (CoFree.Deterministic.of_same hs).2⟩

theorem not_safe_of_hasOutcome_ub {u : UB} (h : HasOutcome t (.ub u)) : ¬Safe t :=
  fun hs => hs.1 u h

theorem not_safe_of_ub {u : UB} {k : WorldOp.Resp (WorldOp.ub u) → CoFree WorldE Empty}
    (h : t.observe = .impure (.ub u) k) : ¬Safe t :=
  not_safe_of_hasOutcome_ub (HasOutcome.halt (o := .ub u) h)

/-- Undefined behavior for one response to a branch is enough to make a run unsafe. -/
theorem not_safe_of_branch_ub {c : Choice} {k : Choice.Resp c → CoFree WorldE Empty} {u : UB}
    (hb : t.observe = .branch c k) (r : Choice.Resp c) (h : HasOutcome (k r) (.ub u)) :
    ¬Safe t :=
  not_safe_of_hasOutcome_ub (.branch r hb h)

/-- A run whose branch responses lead to different outcomes is unsafe, though it may have no UB. -/
theorem not_safe_of_branch_outcomes {c : Choice} {k : Choice.Resp c → CoFree WorldE Empty}
    {r₁ r₂ : Choice.Resp c} {k₁ : WorldOp.Resp o.op → CoFree WorldE Empty}
    {k₂ : WorldOp.Resp o'.op → CoFree WorldE Empty} (hb : t.observe = .branch c k)
    (h₁ : (k r₁).observe = .impure o.op k₁) (h₂ : (k r₂).observe = .impure o'.op k₂)
    (hne : o ≠ o') : ¬Safe t := fun hs =>
  hne ((HasOutcome.halt_iff h₂).1 ((Deterministic.hasOutcome_branch hs.2 hb r₁ r₂).1 (.halt h₁)))

theorem safe_spin : Safe (CoFree.spin : CoFree WorldE Empty) :=
  ⟨fun _ => not_hasOutcome_spin, CoFree.spin_relates_to_self⟩

end Host
