import Sir.Same
import ITree.Same.Theorems

namespace Sir

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
theorem Same.alloc {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {c₁ c₂ : Choice}
    {k₁ : Choice.Resp c₁ → CoFree Exec A} {k₂ : Choice.Resp c₂ → CoFree Exec B}
    (h₁ : t₁.observe = .branch c₁ k₁) (h₂ : t₂.observe = .branch c₂ k₂)
    (h : ∀ r₁ r₂, Same Ret (k₁ r₁) (k₂ r₂)) : Same Ret t₁ t₂ :=
  CoFree.Same.branch h₁ h₂ h

/-- Only the left run allocates here; it must agree for every placement. -/
theorem Same.allocL {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {c : Choice}
    {k : Choice.Resp c → CoFree Exec A} (h₁ : t₁.observe = .branch c k)
    (h : ∀ r, Same Ret (k r) t₂) : Same Ret t₁ t₂ :=
  CoFree.Same.branchL c h₁ h

theorem Same.allocR {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {c : Choice}
    {k : Choice.Resp c → CoFree Exec B} (h₂ : t₂.observe = .branch c k)
    (h : ∀ r, Same Ret t₁ (k r)) : Same Ret t₁ t₂ :=
  CoFree.Same.branchR c h₂ h

/-- A related run, specialised to one placement of a left allocation. -/
theorem Same.allocL_inv {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B}
    {c : Choice} {k : Choice.Resp c → CoFree Exec A} (h : Same Ret t₁ t₂)
    (h₁ : t₁.observe = .branch c k) (r : Choice.Resp c) : Same Ret (k r) t₂ :=
  CoFree.Same.branchL_inv h h₁ r

theorem Same.allocR_inv {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B}
    {c : Choice} {k : Choice.Resp c → CoFree Exec B} (h : Same Ret t₁ t₂)
    (h₂ : t₂.observe = .branch c k) (r : Choice.Resp c) : Same Ret t₁ (k r) :=
  CoFree.Same.branchR_inv h h₂ r

theorem Same.silentL {Ret : A → B → Prop} {t₁ n : CoFree Exec A} {t₂ : CoFree Exec B}
    (h₁ : t₁.observe = .silent n) (h : Same Ret n t₂) : Same Ret t₁ t₂ :=
  CoFree.Same.silentL h₁ h

theorem Same.silentR {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ n : CoFree Exec B}
    (h₂ : t₂.observe = .silent n) (h : Same Ret t₁ n) : Same Ret t₁ t₂ :=
  CoFree.Same.silentR h₂ h

theorem Same.silentL_inv {Ret : A → B → Prop} {t₁ n : CoFree Exec A} {t₂ : CoFree Exec B}
    (h : Same Ret t₁ t₂) (h₁ : t₁.observe = .silent n) : Same Ret n t₂ :=
  CoFree.Same.silentL_inv h h₁

theorem Same.silentR_inv {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ n : CoFree Exec B}
    (h : Same Ret t₁ t₂) (h₂ : t₂.observe = .silent n) : Same Ret t₁ n :=
  CoFree.Same.silentR_inv h h₂

/-- Undefined behavior relates to the same undefined behavior. -/
theorem Same.ub {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {u : UB}
    {k₁ : HostOp.Resp (.fault (.ub u)) → CoFree Exec A}
    {k₂ : HostOp.Resp (.fault (.ub u)) → CoFree Exec B}
    (h₁ : t₁.observe = .impure (.fault (.ub u)) k₁)
    (h₂ : t₂.observe = .impure (.fault (.ub u)) k₂) : Same Ret t₁ t₂ :=
  CoFree.Same.impure _ h₁ h₂ fun r => nomatch r

/-- Both runs perform the same visible operation, and agree for every answer. -/
theorem Same.visible {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {op : HostOp}
    {k₁ : HostOp.Resp op → CoFree Exec A} {k₂ : HostOp.Resp op → CoFree Exec B}
    (h₁ : t₁.observe = .impure op k₁) (h₂ : t₂.observe = .impure op k₂)
    (h : ∀ r, Same Ret (k₁ r) (k₂ r)) : Same Ret t₁ t₂ :=
  CoFree.Same.impure op h₁ h₂ h

/-- Related runs perform the same next visible operation. -/
theorem Same.visible_inv {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B}
    {op₁ op₂ : HostOp} {k₁ : HostOp.Resp op₁ → CoFree Exec A} {k₂ : HostOp.Resp op₂ → CoFree Exec B}
    (h : Same Ret t₁ t₂) (h₁ : t₁.observe = .impure op₁ k₁) (h₂ : t₂.observe = .impure op₂ k₂) :
    op₁ = op₂ :=
  CoFree.Same.impure_inv h h₁ h₂

/-- Undefined behavior is related to no other visible operation. -/
theorem Same.ub_inv {Ret : A → B → Prop} {t₁ : CoFree Exec A} {t₂ : CoFree Exec B} {u : UB}
    {op : HostOp} {k₁ : HostOp.Resp (.fault (.ub u)) → CoFree Exec A}
    {k₂ : HostOp.Resp op → CoFree Exec B}
    (h : Same Ret t₁ t₂) (h₁ : t₁.observe = .impure (.fault (.ub u)) k₁)
    (h₂ : t₂.observe = .impure op k₂) (hub : op ≠ .fault (.ub u)) : False :=
  hub (Same.visible_inv h h₁ h₂).symm

end Sir
