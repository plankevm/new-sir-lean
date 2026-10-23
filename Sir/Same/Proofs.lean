import Sir.Same
import ITree.Same.Theorems

namespace Sir

open CoFree (Next)

variable {A B : Type}

theorem Same.symm {t₁ t₂ : CoFree Exec A} (h : Same Eq t₁ t₂) : Same Eq t₂ t₁ :=
  (CoFree.Same.symm h).mono fun _ _ h => h.symm

theorem Same.trans {t₁ t₂ t₃ : CoFree Exec A} (h₁ : Same Eq t₁ t₂) (h₂ : Same Eq t₂ t₃) :
    Same Eq t₁ t₃ :=
  (CoFree.Same.trans h₁ h₂).mono fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂

/-- Only deterministic runs are related to anything. -/
theorem Deterministic.of_same {t₁ t₂ : CoFree Exec A} (h : Same Eq t₁ t₂) :
    Deterministic t₁ ∧ Deterministic t₂ :=
  ⟨h.trans h.symm, h.symm.trans h⟩

/-- Both runs allocate; they must agree for every pair of placements. -/
theorem Same.alloc {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {c₁ c₂ : Choice}
    {k₁ : Choice.Resp c₁ → CoFree Exec A} {k₂ : Choice.Resp c₂ → CoFree Exec B}
    (h₁ : t₁.observe = .branch c₁ k₁) (h₂ : t₂.observe = .branch c₂ k₂)
    (h : ∀ r₁ r₂, Same RR (k₁ r₁) (k₂ r₂)) : Same RR t₁ t₂ :=
  CoFree.Same.silent (CoFree.silent_of_branch h₁) (CoFree.silent_of_branch h₂) fun n₁ n₂ hn₁ hn₂ => by
    obtain ⟨r₁, rfl⟩ := (CoFree.next_branch_iff h₁).mp hn₁
    obtain ⟨r₂, rfl⟩ := (CoFree.next_branch_iff h₂).mp hn₂
    exact h r₁ r₂

/-- Only the left run allocates here; it must agree for every placement. -/
theorem Same.allocL {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {c : Choice}
    {k : Choice.Resp c → CoFree Exec A} (h₁ : t₁.observe = .branch c k)
    (h : ∀ r, Same RR (k r) t₂) : Same RR t₁ t₂ :=
  CoFree.Same.silentL (CoFree.silent_of_branch h₁) fun n hn => by
    obtain ⟨r, rfl⟩ := (CoFree.next_branch_iff h₁).mp hn
    exact h r

theorem Same.allocR {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {c : Choice}
    {k : Choice.Resp c → CoFree Exec B} (h₂ : t₂.observe = .branch c k)
    (h : ∀ r, Same RR t₁ (k r)) : Same RR t₁ t₂ :=
  CoFree.Same.silentR (CoFree.silent_of_branch h₂) fun n hn => by
    obtain ⟨r, rfl⟩ := (CoFree.next_branch_iff h₂).mp hn
    exact h r

/-- A related run, specialised to one placement of a left allocation. -/
theorem Same.allocL_inv {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B}
    {c : Choice} {k : Choice.Resp c → CoFree Exec A} (h : Same RR t₁ t₂)
    (h₁ : t₁.observe = .branch c k) (r : Choice.Resp c) : Same RR (k r) t₂ :=
  CoFree.Same.silentL_inv h ((CoFree.next_branch_iff h₁).mpr ⟨r, rfl⟩)

theorem Same.allocR_inv {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B}
    {c : Choice} {k : Choice.Resp c → CoFree Exec B} (h : Same RR t₁ t₂)
    (h₂ : t₂.observe = .branch c k) (r : Choice.Resp c) : Same RR t₁ (k r) :=
  CoFree.Same.silentR_inv h ((CoFree.next_branch_iff h₂).mpr ⟨r, rfl⟩)

theorem Same.silentL {RR : A → B → Prop} {t₁ n : CoFree Exec A} {t₂ : CoFree Exec B}
    (h₁ : t₁.observe = .silent n) (h : Same RR n t₂) : Same RR t₁ t₂ :=
  CoFree.Same.silentL (CoFree.silent_of_silent h₁) fun _ hn => (CoFree.next_silent_iff h₁).mp hn ▸ h

theorem Same.silentR {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ n : CoFree Exec B}
    (h₂ : t₂.observe = .silent n) (h : Same RR t₁ n) : Same RR t₁ t₂ :=
  CoFree.Same.silentR (CoFree.silent_of_silent h₂) fun _ hn => (CoFree.next_silent_iff h₂).mp hn ▸ h

theorem Same.silentL_inv {RR : A → B → Prop} {t₁ n : CoFree Exec A} {t₂ : CoFree Exec B}
    (h : Same RR t₁ t₂) (h₁ : t₁.observe = .silent n) : Same RR n t₂ :=
  CoFree.Same.silentL_inv h (.inl h₁)

theorem Same.silentR_inv {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ n : CoFree Exec B}
    (h : Same RR t₁ t₂) (h₂ : t₂.observe = .silent n) : Same RR t₁ n :=
  CoFree.Same.silentR_inv h (.inl h₂)

/-- Undefined behavior relates to undefined behavior of any kind. -/
theorem Same.ub {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {u₁ u₂ : UB}
    {k₁ : HostOp.Resp (.fault (.ub u₁)) → CoFree Exec A}
    {k₂ : HostOp.Resp (.fault (.ub u₂)) → CoFree Exec B}
    (h₁ : t₁.observe = .impure (.fault (.ub u₁)) k₁)
    (h₂ : t₂.observe = .impure (.fault (.ub u₂)) k₂) : Same RR t₁ t₂ :=
  CoFree.Same.fold (.ub _ _ h₁ h₂ rfl rfl)

/-- Both runs perform the same visible operation, and agree for every answer. -/
theorem Same.visible {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {op : HostOp}
    {k₁ : HostOp.Resp op → CoFree Exec A} {k₂ : HostOp.Resp op → CoFree Exec B}
    (h₁ : t₁.observe = .impure op k₁) (h₂ : t₂.observe = .impure op k₂)
    (h : ∀ r, Same RR (k₁ r) (k₂ r)) : Same RR t₁ t₂ :=
  CoFree.Same.fold (.impure op h₁ h₂ h)

/-- Related runs perform the same next visible operation, unless it is undefined behavior. -/
theorem Same.visible_inv {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B}
    {op₁ op₂ : HostOp} {k₁ : HostOp.Resp op₁ → CoFree Exec A} {k₂ : HostOp.Resp op₂ → CoFree Exec B}
    (h : Same RR t₁ t₂) (h₁ : t₁.observe = .impure op₁ k₁) (h₂ : t₂.observe = .impure op₂ k₂)
    (hub : op₁.isUB = false) : op₁ = op₂ :=
  CoFree.Same.impure_inv h h₁ h₂ (by simp [hub])

/-- Undefined behavior is related to no visible operation. -/
theorem Same.ub_inv {RR : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {u : UB}
    {op : HostOp} {k₁ : HostOp.Resp (.fault (.ub u)) → CoFree Exec A}
    {k₂ : HostOp.Resp op → CoFree Exec B}
    (h : Same RR t₁ t₂) (h₁ : t₁.observe = .impure (.fault (.ub u)) k₁)
    (h₂ : t₂.observe = .impure op k₂) (hub : op.isUB = false) : False := by
  have := CoFree.Same.impure_inv (CoFree.Same.symm h) h₂ h₁ (by simp [hub])
  subst this
  simp [HostOp.isUB] at hub

end Sir
