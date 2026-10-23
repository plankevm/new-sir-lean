import Sir.Same
import ITree.Same.Theorems

namespace Sir

open CoFree (Next)

variable {A B : Type}

theorem Same.symm {t₁ t₂ : CoFree Host A} (h : Same Eq t₁ t₂) : Same Eq t₂ t₁ :=
  (CoFree.Same.symm h).mono fun _ _ h => h.symm

theorem Same.trans {t₁ t₂ t₃ : CoFree Host A} (h₁ : Same Eq t₁ t₂) (h₂ : Same Eq t₂ t₃) :
    Same Eq t₁ t₃ :=
  (CoFree.Same.trans h₁ h₂).mono fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂

/-- Only deterministic runs are related to anything. -/
theorem Deterministic.of_same {t₁ t₂ : CoFree Host A} (h : Same Eq t₁ t₂) :
    Deterministic t₁ ∧ Deterministic t₂ :=
  ⟨h.trans h.symm, h.symm.trans h⟩

/-- Both runs allocate; they must agree for every pair of placements. -/
theorem Same.alloc {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B}
    {size₁ size₂ : Nat} {live₁ live₂ : List (Nat × Nat)}
    {k₁ : HostOp.Resp (.alloc size₁ live₁) → CoFree Host A}
    {k₂ : HostOp.Resp (.alloc size₂ live₂) → CoFree Host B}
    (h₁ : t₁.observe = .impure (.alloc size₁ live₁) k₁)
    (h₂ : t₂.observe = .impure (.alloc size₂ live₂) k₂)
    (r₁ : HostOp.Resp (.alloc size₁ live₁)) (r₂ : HostOp.Resp (.alloc size₂ live₂))
    (h : ∀ r₁ r₂, Same RR (k₁ r₁) (k₂ r₂)) : Same RR t₁ t₂ :=
  CoFree.Same.silent (CoFree.silent_of_hidden (hidden := Hidden) h₁ rfl r₁) (CoFree.silent_of_hidden (hidden := Hidden) h₂ rfl r₂)
    fun n₁ n₂ hn₁ hn₂ => by
      obtain ⟨r₁, rfl⟩ := (CoFree.next_hidden_iff (hidden := Hidden) h₁ rfl).mp hn₁
      obtain ⟨r₂, rfl⟩ := (CoFree.next_hidden_iff (hidden := Hidden) h₂ rfl).mp hn₂
      exact h r₁ r₂

/-- Only the left run allocates here; it must agree for every placement. -/
theorem Same.allocL {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B}
    {size : Nat} {live : List (Nat × Nat)} {k : HostOp.Resp (.alloc size live) → CoFree Host A}
    (h₁ : t₁.observe = .impure (.alloc size live) k) (r : HostOp.Resp (.alloc size live))
    (h : ∀ r, Same RR (k r) t₂) : Same RR t₁ t₂ :=
  CoFree.Same.silentL (CoFree.silent_of_hidden (hidden := Hidden) h₁ rfl r) fun n hn => by
    obtain ⟨r, rfl⟩ := (CoFree.next_hidden_iff (hidden := Hidden) h₁ rfl).mp hn
    exact h r

theorem Same.allocR {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B}
    {size : Nat} {live : List (Nat × Nat)} {k : HostOp.Resp (.alloc size live) → CoFree Host B}
    (h₂ : t₂.observe = .impure (.alloc size live) k) (r : HostOp.Resp (.alloc size live))
    (h : ∀ r, Same RR t₁ (k r)) : Same RR t₁ t₂ :=
  CoFree.Same.silentR (CoFree.silent_of_hidden (hidden := Hidden) h₂ rfl r) fun n hn => by
    obtain ⟨r, rfl⟩ := (CoFree.next_hidden_iff (hidden := Hidden) h₂ rfl).mp hn
    exact h r

/-- A related run, specialised to one placement of a left allocation. -/
theorem Same.allocL_inv {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B}
    {size : Nat} {live : List (Nat × Nat)} {k : HostOp.Resp (.alloc size live) → CoFree Host A}
    (h : Same RR t₁ t₂) (h₁ : t₁.observe = .impure (.alloc size live) k)
    (r : HostOp.Resp (.alloc size live)) : Same RR (k r) t₂ :=
  CoFree.Same.silentL_inv h ((CoFree.next_hidden_iff (hidden := Hidden) h₁ rfl).mpr ⟨r, rfl⟩)

theorem Same.allocR_inv {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B}
    {size : Nat} {live : List (Nat × Nat)} {k : HostOp.Resp (.alloc size live) → CoFree Host B}
    (h : Same RR t₁ t₂) (h₂ : t₂.observe = .impure (.alloc size live) k)
    (r : HostOp.Resp (.alloc size live)) : Same RR t₁ (k r) :=
  CoFree.Same.silentR_inv h ((CoFree.next_hidden_iff (hidden := Hidden) h₂ rfl).mpr ⟨r, rfl⟩)

theorem Same.silentL {RR : A → B → Prop} {t₁ n : CoFree Host A} {t₂ : CoFree Host B}
    (h₁ : t₁.observe = .silent n) (h : Same RR n t₂) : Same RR t₁ t₂ :=
  CoFree.Same.silentL (CoFree.silent_of_silent h₁) fun _ hn => (CoFree.next_silent_iff h₁).mp hn ▸ h

theorem Same.silentR {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ n : CoFree Host B}
    (h₂ : t₂.observe = .silent n) (h : Same RR t₁ n) : Same RR t₁ t₂ :=
  CoFree.Same.silentR (CoFree.silent_of_silent h₂) fun _ hn => (CoFree.next_silent_iff h₂).mp hn ▸ h

theorem Same.silentL_inv {RR : A → B → Prop} {t₁ n : CoFree Host A} {t₂ : CoFree Host B}
    (h : Same RR t₁ t₂) (h₁ : t₁.observe = .silent n) : Same RR n t₂ :=
  CoFree.Same.silentL_inv h (.inl h₁)

theorem Same.silentR_inv {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ n : CoFree Host B}
    (h : Same RR t₁ t₂) (h₂ : t₂.observe = .silent n) : Same RR t₁ n :=
  CoFree.Same.silentR_inv h (.inl h₂)

/-- Undefined behavior relates to undefined behavior of any kind. -/
theorem Same.ub {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B} {u₁ u₂ : UB}
    {k₁ : HostOp.Resp (.fault (.ub u₁)) → CoFree Host A}
    {k₂ : HostOp.Resp (.fault (.ub u₂)) → CoFree Host B}
    (h₁ : t₁.observe = .impure (.fault (.ub u₁)) k₁)
    (h₂ : t₂.observe = .impure (.fault (.ub u₂)) k₂) : Same RR t₁ t₂ :=
  CoFree.Same.fold (.ub _ _ h₁ h₂ rfl rfl Bool.false_ne_true Bool.false_ne_true)

/-- Both runs perform the same visible operation, and agree for every answer. -/
theorem Same.visible {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B} {op : HostOp}
    {k₁ : HostOp.Resp op → CoFree Host A} {k₂ : HostOp.Resp op → CoFree Host B}
    (h₁ : t₁.observe = .impure op k₁) (h₂ : t₂.observe = .impure op k₂)
    (hop : op.isAlloc = false) (h : ∀ r, Same RR (k₁ r) (k₂ r)) : Same RR t₁ t₂ :=
  CoFree.Same.fold (.impure op h₁ h₂ (by simp [hop]) h)

/-- Related runs perform the same next visible operation, unless it is undefined behavior. -/
theorem Same.visible_inv {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B}
    {op₁ op₂ : HostOp} {k₁ : HostOp.Resp op₁ → CoFree Host A} {k₂ : HostOp.Resp op₂ → CoFree Host B}
    (h : Same RR t₁ t₂) (h₁ : t₁.observe = .impure op₁ k₁) (h₂ : t₂.observe = .impure op₂ k₂)
    (hop₁ : op₁.isAlloc = false) (hop₂ : op₂.isAlloc = false) (hub : op₁.isUB = false) :
    op₁ = op₂ :=
  CoFree.Same.impure_inv h h₁ h₂ (by simp [hop₁]) (by simp [hop₂]) (by simp [hub])

/-- Undefined behavior is related to no visible operation. -/
theorem Same.ub_inv {RR : A → B → Prop} {t₁ : CoFree Host A} {t₂ : CoFree Host B} {u : UB}
    {op : HostOp} {k₁ : HostOp.Resp (.fault (.ub u)) → CoFree Host A}
    {k₂ : HostOp.Resp op → CoFree Host B}
    (h : Same RR t₁ t₂) (h₁ : t₁.observe = .impure (.fault (.ub u)) k₁)
    (h₂ : t₂.observe = .impure op k₂) (hop : op.isAlloc = false) (hub : op.isUB = false) : False := by
  have := CoFree.Same.impure_inv (CoFree.Same.symm h) h₂ h₁ (by simp [hop])
    (Bool.false_ne_true) (by simp [hub])
  subst this
  simp [HostOp.isUB] at hub

end Sir
