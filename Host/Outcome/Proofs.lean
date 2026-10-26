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

/-! ## Halting as a result -/

section CatchHalt

open CoFree (Same SameFinite ForallUnobserved Returns)

variable {t t' : CoFree WorldE Empty} {o : Outcome}

universe w₁ w₂ in
theorem catchStep_map {X : Type w₁} {Y : Type w₂} (f : X → Y) (x : Step WorldE Empty X) :
    catchStep (x.map f) = (catchStep x).map f := by
  cases x with
  | pure e => nomatch e
  | impure op k => simp only [Step.map, catchStep]; split <;> rfl
  | _ => rfl

theorem observe_catchHalt (t : CoFree WorldE Empty) :
    (catchHalt t).observe = catchStep (t.observe.map catchHalt) := by
  obtain ⟨S, J, s₀, step, target⟩ := t
  simp only [CoFree.observe, catchHalt, catchStep_map, Step.map_map]
  refine Step.map_congr (fun x => ?_) _
  cases x <;> rfl

theorem catchHalt_silent (h : t.observe = .silent t') :
    (catchHalt t).observe = .silent (catchHalt t') := by
  rw [observe_catchHalt, h]; rfl

theorem catchHalt_branch {c : Choice} {k : Choice.Resp c → CoFree WorldE Empty}
    (h : t.observe = .branch c k) : (catchHalt t).observe = .branch c fun r => catchHalt (k r) := by
  rw [observe_catchHalt, h]; rfl

theorem catchHalt_halt {op : WorldOp} {k : WorldOp.Resp op → CoFree WorldE Empty}
    (h : t.observe = .impure op k) (hop : WorldOp.Resp op → False) :
    (catchHalt t).observe = .pure (.ofOp op hop) := by
  rw [observe_catchHalt, h]; simp only [Step.map, catchStep, dite_eq_left_of_eq_true (eq_true hop)]

theorem catchHalt_impure {op : WorldOp} {k : WorldOp.Resp op → CoFree WorldE Empty}
    (h : t.observe = .impure op k) (hop : ¬(WorldOp.Resp op → False)) :
    (catchHalt t).observe = .impure op fun r => catchHalt (k r) := by
  rw [observe_catchHalt, h]; simp only [Step.map, catchStep, dite_eq_right_of_eq_false (eq_false hop)]; rfl

theorem catchHalt_pure_inv (h : (catchHalt t).observe = .pure o) :
    ∃ op k hop, t.observe = .impure op k ∧ o = .ofOp op hop := by
  rw [observe_catchHalt] at h
  cases ht : t.observe with
  | pure e => nomatch e
  | impure op k =>
    rw [ht] at h
    by_cases hop : WorldOp.Resp op → False
    · simp only [Step.map, catchStep, dite_eq_left_of_eq_true (eq_true hop)] at h; cases h; exact ⟨op, k, hop, rfl, rfl⟩
    · simp only [Step.map, catchStep, dite_eq_right_of_eq_false (eq_false hop)] at h; cases h
  | _ => rw [ht] at h; cases h

theorem catchHalt_impure_inv {op : WorldOp} {c : WorldOp.Resp op → CoFree WorldE Outcome}
    (h : (catchHalt t).observe = .impure op c) :
    ∃ k, t.observe = .impure op k ∧ c = fun r => catchHalt (k r) := by
  rw [observe_catchHalt] at h
  cases ht : t.observe with
  | pure e => nomatch e
  | impure op' k =>
    rw [ht] at h
    by_cases hop : WorldOp.Resp op' → False
    · simp only [Step.map, catchStep, dite_eq_left_of_eq_true (eq_true hop)] at h; cases h
    · simp only [Step.map, catchStep, dite_eq_right_of_eq_false (eq_false hop)] at h; cases h; exact ⟨k, rfl, rfl⟩
  | _ => rw [ht] at h; cases h

theorem catchHalt_silent_inv {x : CoFree WorldE Outcome} (h : (catchHalt t).observe = .silent x) :
    ∃ t', t.observe = .silent t' ∧ x = catchHalt t' := by
  rw [observe_catchHalt] at h
  cases ht : t.observe with
  | pure e => nomatch e
  | silent t' => rw [ht] at h; cases h; exact ⟨t', rfl, rfl⟩
  | impure op k =>
    rw [ht] at h
    by_cases hop : WorldOp.Resp op → False
    · simp only [Step.map, catchStep, dite_eq_left_of_eq_true (eq_true hop)] at h; cases h
    · simp only [Step.map, catchStep, dite_eq_right_of_eq_false (eq_false hop)] at h; cases h
  | branch => rw [ht] at h; cases h

theorem catchHalt_branch_inv {c : Choice} {k' : Choice.Resp c → CoFree WorldE Outcome}
    (h : (catchHalt t).observe = .branch c k') :
    ∃ k, t.observe = .branch c k ∧ k' = fun r => catchHalt (k r) := by
  rw [observe_catchHalt] at h
  cases ht : t.observe with
  | pure e => nomatch e
  | branch c' k => rw [ht] at h; cases h; exact ⟨k, rfl, rfl⟩
  | impure op k =>
    rw [ht] at h
    by_cases hop : WorldOp.Resp op → False
    · simp only [Step.map, catchStep, dite_eq_left_of_eq_true (eq_true hop)] at h; cases h
    · simp only [Step.map, catchStep, dite_eq_right_of_eq_false (eq_false hop)] at h; cases h
  | silent => rw [ht] at h; cases h

theorem forallUnobserved_catchHalt {p : CoFree WorldE Outcome → Prop} :
    ForallUnobserved (catchHalt t) p ↔ ForallUnobserved t fun t' => p (catchHalt t') := by
  unfold ForallUnobserved
  rw [observe_catchHalt]
  cases t.observe with
  | pure e => nomatch e
  | impure op k =>
    by_cases hop : WorldOp.Resp op → False
    · simp only [Step.map, catchStep, dite_eq_left_of_eq_true (eq_true hop)]
    · simp only [Step.map, catchStep, dite_eq_right_of_eq_false (eq_false hop)]
  | _ => rfl

/-- A run ends with `o` exactly when its `catchHalt` returns `o`. -/
theorem hasOutcome_iff_returns : HasOutcome t o ↔ Returns (catchHalt t) o := by
  constructor
  · intro h
    induction h with
    | halt hop hk => exact .pure (catchHalt_halt hk hop)
    | silent hs _ ih => exact .silent (catchHalt_silent hs) ih
    | branch r hb _ ih => exact .branch r (catchHalt_branch hb) ih
    | impure r hi _ ih => exact .impure r (catchHalt_impure hi fun h => h r) ih
  · suffices ∀ x, Returns x o → ∀ t, x = catchHalt t → HasOutcome t o from fun h => this _ h t rfl
    intro x h
    induction h with
    | pure hx =>
      rintro t rfl
      obtain ⟨op, k, hop, ht, rfl⟩ := catchHalt_pure_inv hx
      exact .halt hop ht
    | silent hx _ ih =>
      rintro t rfl
      obtain ⟨t', ht, rfl⟩ := catchHalt_silent_inv hx
      exact .silent ht (ih t' rfl)
    | impure r hx _ ih =>
      rintro t rfl
      obtain ⟨k, ht, rfl⟩ := catchHalt_impure_inv hx
      exact .impure r ht (ih _ rfl)
    | branch r hx _ ih =>
      rintro t rfl
      obtain ⟨k, ht, rfl⟩ := catchHalt_branch_inv hx
      exact .branch r ht (ih _ rfl)

private theorem sameFinite_catchHalt {Ret : Empty → Empty → Prop}
    {R : CoFree WorldE Empty → CoFree WorldE Empty → Prop} {t₁ t₂ : CoFree WorldE Empty}
    (h : SameFinite Ret R t₁ t₂) :
    SameFinite Eq (fun x y => ∃ t₁ t₂, R t₁ t₂ ∧ x = catchHalt t₁ ∧ y = catchHalt t₂)
      (catchHalt t₁) (catchHalt t₂) := by
  induction h with
  | ret a => nomatch a
  | impure op h₁ h₂ hrec =>
    by_cases hop : WorldOp.Resp op → False
    · exact .ret _ _ (catchHalt_halt h₁ hop) (catchHalt_halt h₂ hop) rfl
    · exact .impure op (catchHalt_impure h₁ hop) (catchHalt_impure h₂ hop)
        fun r => ⟨_, _, hrec r, rfl, rfl⟩
  | silentL h _ ih => exact .silentL (catchHalt_silent h) ih
  | silentR h _ ih => exact .silentR (catchHalt_silent h) ih
  | branchL c h _ ih => exact .branchL c (catchHalt_branch h) ih
  | branchR c h _ ih => exact .branchR c (catchHalt_branch h) ih
  | mutualUnobservedStep h =>
    refine .mutualUnobservedStep (forallUnobserved_catchHalt.2 ?_)
    refine CoFree.forallUnobserved_mono h fun t₁' h' => forallUnobserved_catchHalt.2 ?_
    exact CoFree.forallUnobserved_mono h' fun t₂' h'' => ⟨_, _, h'', rfl, rfl⟩

private theorem sameFinite_of_catchHalt {Ret : Empty → Empty → Prop} {x y : CoFree WorldE Outcome}
    (h : SameFinite Eq (Same Eq) x y) :
    ∀ t₁ t₂, x = catchHalt t₁ → y = catchHalt t₂ →
      SameFinite Ret (fun t₁ t₂ => Same Eq (catchHalt t₁) (catchHalt t₂)) t₁ t₂ := by
  induction h with
  | ret a b h₁ h₂ hab =>
    rintro t₁ t₂ rfl rfl
    obtain ⟨op₁, k₁, hop₁, ht₁, rfl⟩ := catchHalt_pure_inv h₁
    obtain ⟨op₂, k₂, hop₂, ht₂, rfl⟩ := catchHalt_pure_inv h₂
    obtain rfl := Outcome.ofOp_injective hab
    exact .impure op₁ ht₁ ht₂ fun r => (hop₁ r).elim
  | impure op h₁ h₂ hrec =>
    rintro t₁ t₂ rfl rfl
    obtain ⟨k₁, ht₁, rfl⟩ := catchHalt_impure_inv h₁
    obtain ⟨k₂, ht₂, rfl⟩ := catchHalt_impure_inv h₂
    exact .impure op ht₁ ht₂ hrec
  | silentL h _ ih =>
    rintro t₁ t₂ rfl rfl
    obtain ⟨t₁', ht, rfl⟩ := catchHalt_silent_inv h
    exact .silentL ht (ih t₁' t₂ rfl rfl)
  | silentR h _ ih =>
    rintro t₁ t₂ rfl rfl
    obtain ⟨t₂', ht, rfl⟩ := catchHalt_silent_inv h
    exact .silentR ht (ih t₁ t₂' rfl rfl)
  | branchL c h _ ih =>
    rintro t₁ t₂ rfl rfl
    obtain ⟨k, ht, rfl⟩ := catchHalt_branch_inv h
    exact .branchL c ht fun r => ih r _ t₂ rfl rfl
  | branchR c h _ ih =>
    rintro t₁ t₂ rfl rfl
    obtain ⟨k, ht, rfl⟩ := catchHalt_branch_inv h
    exact .branchR c ht fun r => ih r t₁ _ rfl rfl
  | mutualUnobservedStep h =>
    rintro t₁ t₂ rfl rfl
    refine .mutualUnobservedStep (CoFree.forallUnobserved_mono (forallUnobserved_catchHalt.1 h) ?_)
    exact fun _ h' => forallUnobserved_catchHalt.1 h'

/-- Two runs are related exactly when they are related with their ends as results. The relation
on `Empty` results says nothing; on outcomes it is `Eq`, a terminal operation relating only to
itself. -/
theorem same_iff_catchHalt {Ret : Empty → Empty → Prop} {t₁ t₂ : CoFree WorldE Empty} :
    Same Ret t₁ t₂ ↔ Same Eq (catchHalt t₁) (catchHalt t₂) := by
  constructor
  · intro h
    refine Same.coind (fun x y => ∃ t₁ t₂, Same Ret t₁ t₂ ∧ x = catchHalt t₁ ∧ y = catchHalt t₂)
      ?_ ⟨t₁, t₂, h, rfl, rfl⟩
    rintro _ _ ⟨t₁, t₂, h, rfl, rfl⟩
    exact SameFinite.mono (fun _ _ h => .inl h) (sameFinite_catchHalt (Same.unfold h))
  · intro h
    refine Same.coind (fun t₁ t₂ => Same Eq (catchHalt t₁) (catchHalt t₂)) ?_ h
    intro t₁ t₂ h
    exact SameFinite.mono (fun _ _ h => .inl h)
      (sameFinite_of_catchHalt (Same.unfold h) t₁ t₂ rfl rfl)

theorem deterministic_iff_catchHalt :
    CoFree.Deterministic t ↔ CoFree.Deterministic (catchHalt t) :=
  same_iff_catchHalt

/-- `Safe` in terms of `catchHalt`: no UB result, and deterministic. -/
theorem safe_iff_catchHalt :
    Safe t ↔ (∀ u, ¬Returns (catchHalt t) (.ub u)) ∧ CoFree.Deterministic (catchHalt t) := by
  simp only [Safe, hasOutcome_iff_returns, deterministic_iff_catchHalt]

end CatchHalt

end Host
