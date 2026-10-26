import Host.Outcome
import ITree.Same.Theorems

namespace Host

/-! ## Outcomes are the terminal operations -/

theorem Outcome.ofOp_injective {op₁ op₂ : WorldOp} {h₁ : WorldOp.Resp op₁ → False}
    {h₂ : WorldOp.Resp op₂ → False} (h : Outcome.ofOp op₁ h₁ = .ofOp op₂ h₂) : op₁ = op₂ := by
  rcases op₁ with _ | _ | ⟨_ | _ | _ | _⟩ <;>
    try exact (h₁ (by unfold WorldOp.Resp; exact default)).elim
  all_goals rcases op₂ with _ | _ | ⟨_ | _ | _ | _⟩ <;>
    try exact (h₂ (by unfold WorldOp.Resp; exact default)).elim
  all_goals simp_all [Outcome.ofOp]

/-! ## One step -/

variable {t t' : CoFree WorldE Empty} {o o' : Outcome}

theorem HasOutcome.congr (h : HasOutcome t o) (he : t.observe = t'.observe) : HasOutcome t' o := by
  cases h with
  | halt hop hk => exact .halt hop (he ▸ hk)
  | silent hs h => exact .silent (he ▸ hs) h
  | branch r hb h => exact .branch r (he ▸ hb) h
  | impure r hi h => exact .impure r (he ▸ hi) h

/-- A run at its terminal operation has exactly that outcome. -/
theorem HasOutcome.halt_iff {op : WorldOp} {k : WorldOp.Resp op → CoFree WorldE Empty}
    (hk : t.observe = .impure op k) (hop : WorldOp.Resp op → False) :
    HasOutcome t o ↔ o = .ofOp op hop := by
  constructor
  · intro h
    cases h with
    | halt _ h => rw [hk] at h; cases h; rfl
    | silent h _ => rw [hk] at h; cases h
    | branch _ h _ => rw [hk] at h; cases h
    | impure r h _ => rw [hk] at h; cases h; exact (hop r).elim
  · rintro rfl; exact .halt hop hk

theorem HasOutcome.silent_iff (hs : t.observe = .silent t') :
    HasOutcome t o ↔ HasOutcome t' o := by
  constructor
  · intro h
    cases h with
    | halt _ h => rw [hs] at h; cases h
    | silent h h' => rw [hs] at h; cases h; exact h'
    | branch _ h _ => rw [hs] at h; cases h
    | impure _ h _ => rw [hs] at h; cases h
  · exact .silent hs

theorem HasOutcome.branch_iff {c : Choice} {k : Choice.Resp c → CoFree WorldE Empty}
    (hb : t.observe = .branch c k) : HasOutcome t o ↔ ∃ r, HasOutcome (k r) o := by
  constructor
  · intro h
    cases h with
    | halt _ h => rw [hb] at h; cases h
    | silent h _ => rw [hb] at h; cases h
    | branch r h h' => rw [hb] at h; cases h; exact ⟨r, h'⟩
    | impure _ h _ => rw [hb] at h; cases h
  · rintro ⟨r, h⟩; exact .branch r hb h

/-- A host operation either ends the run with `o`, or some answer to it leads to `o`. -/
theorem HasOutcome.impure_iff {op : WorldOp} {k : WorldOp.Resp op → CoFree WorldE Empty}
    (hi : t.observe = .impure op k) :
    HasOutcome t o ↔ (∃ hop, o = .ofOp op hop) ∨ ∃ r, HasOutcome (k r) o := by
  constructor
  · intro h
    cases h with
    | halt hop h => rw [hi] at h; cases h; exact .inl ⟨hop, rfl⟩
    | silent h _ => rw [hi] at h; cases h
    | branch _ h _ => rw [hi] at h; cases h
    | impure r h h' => rw [hi] at h; cases h; exact .inr ⟨r, h'⟩
  · rintro (⟨hop, rfl⟩ | ⟨r, h⟩)
    · exact .halt hop hi
    · exact .impure r hi h

/-- A terminal operation gives the run an outcome. -/
theorem HasOutcome.of_terminal {op : WorldOp} {k : WorldOp.Resp op → CoFree WorldE Empty}
    (hi : t.observe = .impure op k) (hop : WorldOp.Resp op → False) : ∃ o, HasOutcome t o :=
  ⟨_, .halt hop hi⟩

theorem not_hasOutcome_spin : ¬HasOutcome (CoFree.spin : CoFree WorldE Empty) o := by
  suffices ∀ t, HasOutcome t o → t = CoFree.spin → False from fun h => this _ h rfl
  intro t h
  induction h with
  | halt _ h => rintro rfl; rw [CoFree.spin_observe] at h; cases h
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
  | halt hop hk =>
    exact hasOutcome_of_sameFinite_impure (CoFree.Same.unfold h) hk fun _ _ hn _ => .halt hop hn
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
  not_safe_of_hasOutcome_ub (.halt Empty.elim h)

/-- Undefined behavior for one response to a branch is enough to make a run unsafe. -/
theorem not_safe_of_branch_ub {c : Choice} {k : Choice.Resp c → CoFree WorldE Empty} {u : UB}
    (hb : t.observe = .branch c k) (r : Choice.Resp c) (h : HasOutcome (k r) (.ub u)) :
    ¬Safe t :=
  not_safe_of_hasOutcome_ub (.branch r hb h)

/-- A run whose branch responses lead to different outcomes is unsafe, though it may have no UB. -/
theorem not_safe_of_branch_outcomes {c : Choice} {k : Choice.Resp c → CoFree WorldE Empty}
    {r₁ r₂ : Choice.Resp c} {op₁ op₂ : WorldOp} {k₁ : WorldOp.Resp op₁ → CoFree WorldE Empty}
    {k₂ : WorldOp.Resp op₂ → CoFree WorldE Empty} (hb : t.observe = .branch c k)
    (h₁ : (k r₁).observe = .impure op₁ k₁) (h₂ : (k r₂).observe = .impure op₂ k₂)
    (hop₁ : WorldOp.Resp op₁ → False) (hop₂ : WorldOp.Resp op₂ → False) (hne : op₁ ≠ op₂) :
    ¬Safe t := fun hs =>
  hne (Outcome.ofOp_injective ((HasOutcome.halt_iff h₂ hop₂).1
    ((Deterministic.hasOutcome_branch hs.2 hb r₁ r₂).1 (.halt hop₁ h₁))))

theorem safe_spin : Safe (CoFree.spin : CoFree WorldE Empty) :=
  ⟨fun _ => not_hasOutcome_spin, CoFree.spin_relates_to_self⟩

end Host
