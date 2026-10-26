import ITree.Same
import ITree.Program
import ITree.Machine.Theorems

universe u

namespace CoFree.Proofs

variable {E : Effect.{u}} {A B C D : Type u}

/-! ## Unobserved steps -/

theorem forallUnobserved_mono {m : CoFree E A} {p q : CoFree E A → Prop}
    (h : ForallUnobserved m p) (hpq : ∀ n, p n → q n) : ForallUnobserved m q := by
  unfold ForallUnobserved at h ⊢
  split at h
  · exact hpq _ h
  · exact fun r => hpq _ (h r)
  · exact h.elim

theorem forallUnobserved_congr {m m' : CoFree E A} {p : CoFree E A → Prop}
    (he : m.observe = m'.observe) (h : ForallUnobserved m p) : ForallUnobserved m' p := by
  unfold ForallUnobserved at h ⊢; rw [← he]; exact h

theorem forallUnobserved_silent {m n : CoFree E A} {p : CoFree E A → Prop}
    (h : m.observe = .silent n) : ForallUnobserved m p ↔ p n := by
  unfold ForallUnobserved; rw [h]

theorem forallUnobserved_branch {m : CoFree E A} {c : E.BrOp} {k : E.BrResp c → CoFree E A}
    {p : CoFree E A → Prop} (h : m.observe = .branch c k) :
    ForallUnobserved m p ↔ ∀ r, p (k r) := by
  unfold ForallUnobserved; rw [h]

theorem not_forallUnobserved_pure {m : CoFree E A} {a : A} {p : CoFree E A → Prop}
    (h : m.observe = .pure a) : ¬ForallUnobserved m p := by
  unfold ForallUnobserved; rw [h]; exact id

theorem not_forallUnobserved_impure {m : CoFree E A} {op : E.Op} {k : E.Resp op → CoFree E A}
    {p : CoFree E A → Prop} (h : m.observe = .impure op k) : ¬ForallUnobserved m p := by
  unfold ForallUnobserved; rw [h]; exact id

/-- An unobserved step has a successor, since every branch has a response. -/
theorem forallUnobserved_exists {m : CoFree E A} {p q : CoFree E A → Prop}
    (hp : ForallUnobserved m p) (hq : ForallUnobserved m q) : ∃ n, p n ∧ q n := by
  unfold ForallUnobserved at hp hq
  split at hp
  · rename_i h; rw [h] at hq; exact ⟨_, hp, hq⟩
  · rename_i c k h
    rw [h] at hq
    obtain ⟨r⟩ := E.brResp_nonempty c
    exact ⟨_, hp r, hq r⟩
  · exact hp.elim

theorem forallUnobserved_swap {m₁ : CoFree E A} {m₂ : CoFree E B}
    {R : CoFree E A → CoFree E B → Prop}
    (h : ForallUnobserved m₁ fun n₁ => ForallUnobserved m₂ (R n₁)) :
    ForallUnobserved m₂ fun n₂ => ForallUnobserved m₁ fun n₁ => R n₁ n₂ := by
  have ⟨n₁, h₂, _⟩ := forallUnobserved_exists h h
  have hm₂ : ForallUnobserved m₂ fun _ => True := forallUnobserved_mono h₂ fun _ _ => trivial
  unfold ForallUnobserved at hm₂
  split at hm₂
  · rename_i h₂
    rw [forallUnobserved_silent h₂]
    exact forallUnobserved_mono h fun _ h => (forallUnobserved_silent h₂).mp h
  · rename_i h₂
    rw [forallUnobserved_branch h₂]
    exact fun r => forallUnobserved_mono h fun _ h => (forallUnobserved_branch h₂).mp h r
  · exact hm₂.elim

theorem forallUnobserved_bind {m : CoFree E A} {f : A → CoFree E B} {p : CoFree E B → Prop}
    (h : ForallUnobserved m fun n => p (n.bind f)) : ForallUnobserved (m.bind f) p := by
  unfold ForallUnobserved at h ⊢
  rw [observe_bind]
  split at h
  · rename_i h'; rw [h']; exact h
  · rename_i h'; rw [h']; exact h
  · exact h.elim

/-! ## One layer -/

section Layer

variable {Ret : A → B → Prop}

/-- Finitely many unobserved steps on the left, as one rule. -/
theorem sameFinite_unobservedL {R : CoFree E A → CoFree E B → Prop} {m₁ : CoFree E A}
    {m₂ : CoFree E B} (h : ForallUnobserved m₁ fun n => SameFinite Ret R n m₂) :
    SameFinite Ret R m₁ m₂ := by
  unfold ForallUnobserved at h
  split at h
  · rename_i h'; exact .silentL h' h
  · rename_i h'; exact .branchL _ h' h
  · exact h.elim

theorem sameFinite_unobservedR {R : CoFree E A → CoFree E B → Prop} {m₁ : CoFree E A}
    {m₂ : CoFree E B} (h : ForallUnobserved m₂ fun n => SameFinite Ret R m₁ n) :
    SameFinite Ret R m₁ m₂ := by
  unfold ForallUnobserved at h
  split at h
  · rename_i h'; exact .silentR h' h
  · rename_i h'; exact .branchR _ h' h
  · exact h.elim

theorem SameFinite.mono {R R' : CoFree E A → CoFree E B → Prop}
    (hR : ∀ x y, R x y → R' x y) {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : SameFinite Ret R m₁ m₂) : SameFinite Ret R' m₁ m₂ := by
  induction h with
  | ret a b h₁ h₂ hab => exact .ret a b h₁ h₂ hab
  | impure op h₁ h₂ hk => exact .impure op h₁ h₂ fun r => hR _ _ (hk r)
  | silentL h₁ _ ih => exact .silentL h₁ ih
  | silentR h₂ _ ih => exact .silentR h₂ ih
  | branchL c h₁ _ ih => exact .branchL c h₁ ih
  | branchR c h₂ _ ih => exact .branchR c h₂ ih
  | mutualUnobservedStep h =>
    exact .mutualUnobservedStep (forallUnobserved_mono h fun _ h =>
      forallUnobserved_mono h fun _ => hR _ _)

theorem SameFinite.congr {R : CoFree E A → CoFree E B → Prop}
    {m₁ m₁' : CoFree E A} {m₂ m₂' : CoFree E B} (h : SameFinite Ret R m₁ m₂)
    (he₁ : m₁.observe = m₁'.observe) (he₂ : m₂.observe = m₂'.observe) :
    SameFinite Ret R m₁' m₂' := by
  induction h generalizing m₁' m₂' with
  | ret a b h₁ h₂ hab => exact .ret a b (he₁ ▸ h₁) (he₂ ▸ h₂) hab
  | impure op h₁ h₂ hk => exact .impure op (he₁ ▸ h₁) (he₂ ▸ h₂) hk
  | silentL h₁ _ ih => exact .silentL (he₁ ▸ h₁) (ih rfl he₂)
  | silentR h₂ _ ih => exact .silentR (he₂ ▸ h₂) (ih he₁ rfl)
  | branchL c h₁ _ ih => exact .branchL c (he₁ ▸ h₁) fun r => ih r rfl he₂
  | branchR c h₂ _ ih => exact .branchR c (he₂ ▸ h₂) fun r => ih r he₁ rfl
  | mutualUnobservedStep h =>
    exact .mutualUnobservedStep (forallUnobserved_congr he₁ (forallUnobserved_mono h fun _ h =>
      forallUnobserved_congr he₂ h))

end Layer

/-! ## The fixed point -/

section Fixpoint

variable {Ret : A → B → Prop}

theorem Same.unfold {m₁ : CoFree E A} {m₂ : CoFree E B} :
    Same Ret m₁ m₂ → SameFinite Ret (Same Ret) m₁ m₂
  | ⟨R, h, hR⟩ => SameFinite.mono (fun _ _ hxy => ⟨R, hxy, hR⟩) (hR _ _ h)

theorem Same.fold {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : SameFinite Ret (Same Ret) m₁ m₂) : Same Ret m₁ m₂ :=
  ⟨SameFinite Ret (Same Ret), h, fun _ _ h => SameFinite.mono (fun _ _ => Same.unfold) h⟩

/-- Coinduction up to `Same`: `R` may step to pairs already known to be related. -/
theorem Same.coind (R : CoFree E A → CoFree E B → Prop)
    (hR : ∀ x y, R x y → SameFinite Ret (fun x y => R x y ∨ Same Ret x y) x y)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : R m₁ m₂) : Same Ret m₁ m₂ := by
  refine ⟨fun x y => R x y ∨ Same Ret x y, .inl h, ?_⟩
  rintro x y (hxy | hxy)
  · exact hR x y hxy
  · exact SameFinite.mono (fun _ _ => .inr) (Same.unfold hxy)

theorem Same.congr {m₁ m₁' : CoFree E A} {m₂ m₂' : CoFree E B}
    (h : Same Ret m₁ m₂) (he₁ : m₁.observe = m₁'.observe)
    (he₂ : m₂.observe = m₂'.observe) : Same Ret m₁' m₂' :=
  Same.fold (SameFinite.congr (Same.unfold h) he₁ he₂)

end Fixpoint

/-! ## Constructors -/

section Constructors

variable {Ret : A → B → Prop}

theorem Same.ret {m₁ : CoFree E A} {m₂ : CoFree E B} {a : A} {b : B}
    (h₁ : m₁.observe = .pure a) (h₂ : m₂.observe = .pure b) (h : Ret a b) :
    Same Ret m₁ m₂ :=
  Same.fold (.ret a b h₁ h₂ h)

theorem Same.impure {m₁ : CoFree E A} {m₂ : CoFree E B} (op : E.Op)
    {k₁ : E.Resp op → CoFree E A} {k₂ : E.Resp op → CoFree E B}
    (h₁ : m₁.observe = .impure op k₁) (h₂ : m₂.observe = .impure op k₂)
    (h : ∀ r, Same Ret (k₁ r) (k₂ r)) : Same Ret m₁ m₂ :=
  Same.fold (.impure op h₁ h₂ h)

theorem Same.silentL {m₁ n₁ : CoFree E A} {m₂ : CoFree E B}
    (h₁ : m₁.observe = .silent n₁) (h : Same Ret n₁ m₂) : Same Ret m₁ m₂ :=
  Same.fold (.silentL h₁ (Same.unfold h))

theorem Same.silentR {m₁ : CoFree E A} {m₂ n₂ : CoFree E B}
    (h₂ : m₂.observe = .silent n₂) (h : Same Ret m₁ n₂) : Same Ret m₁ m₂ :=
  Same.fold (.silentR h₂ (Same.unfold h))

theorem Same.branchL {m₁ : CoFree E A} {m₂ : CoFree E B} (c : E.BrOp)
    {k : E.BrResp c → CoFree E A} (h₁ : m₁.observe = .branch c k)
    (h : ∀ r, Same Ret (k r) m₂) : Same Ret m₁ m₂ :=
  Same.fold (.branchL c h₁ fun r => Same.unfold (h r))

theorem Same.branchR {m₁ : CoFree E A} {m₂ : CoFree E B} (c : E.BrOp)
    {k : E.BrResp c → CoFree E B} (h₂ : m₂.observe = .branch c k)
    (h : ∀ r, Same Ret m₁ (k r)) : Same Ret m₁ m₂ :=
  Same.fold (.branchR c h₂ fun r => Same.unfold (h r))

theorem Same.mutualUnobservedStep {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : ForallUnobserved m₁ fun n₁ => ForallUnobserved m₂ (Same Ret n₁)) : Same Ret m₁ m₂ :=
  Same.fold (.mutualUnobservedStep h)

/-- Both sides branch: every pair of responses must be related. -/
theorem Same.branch {m₁ : CoFree E A} {m₂ : CoFree E B} {c₁ c₂ : E.BrOp}
    {k₁ : E.BrResp c₁ → CoFree E A} {k₂ : E.BrResp c₂ → CoFree E B}
    (h₁ : m₁.observe = .branch c₁ k₁) (h₂ : m₂.observe = .branch c₂ k₂)
    (h : ∀ r₁ r₂, Same Ret (k₁ r₁) (k₂ r₂)) : Same Ret m₁ m₂ :=
  Same.branchL c₁ h₁ fun r₁ => Same.branchR c₂ h₂ (h r₁)

end Constructors

/-! ## Inversion -/

section Inversion

variable {Ret : A → B → Prop}

theorem Same.silentL_inv {m₁ n₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .silent n₁) : Same Ret n₁ m₂ := by
  replace h := Same.unfold h
  induction h generalizing n₁ with
  | ret _ _ h₁' => rw [h₁] at h₁'; cases h₁'
  | impure _ h₁' => rw [h₁] at h₁'; cases h₁'
  | silentL h₁' h => rw [h₁] at h₁'; cases h₁'; exact Same.fold h
  | silentR h₂ _ ih => exact Same.silentR h₂ (ih h₁)
  | branchL _ h₁' => rw [h₁] at h₁'; cases h₁'
  | branchR c h₂ _ ih => exact Same.branchR c h₂ fun r => ih r h₁
  | mutualUnobservedStep h =>
    rw [forallUnobserved_silent h₁] at h
    exact Same.fold (sameFinite_unobservedR (forallUnobserved_mono h fun _ => Same.unfold))

theorem Same.silentR_inv {m₁ : CoFree E A} {m₂ n₂ : CoFree E B}
    (h : Same Ret m₁ m₂) (h₂ : m₂.observe = .silent n₂) : Same Ret m₁ n₂ := by
  replace h := Same.unfold h
  induction h generalizing n₂ with
  | ret _ _ _ h₂' => rw [h₂] at h₂'; cases h₂'
  | impure _ _ h₂' => rw [h₂] at h₂'; cases h₂'
  | silentL h₁ _ ih => exact Same.silentL h₁ (ih h₂)
  | silentR h₂' h => rw [h₂] at h₂'; cases h₂'; exact Same.fold h
  | branchL c h₁ _ ih => exact Same.branchL c h₁ fun r => ih r h₂
  | branchR _ h₂' => rw [h₂] at h₂'; cases h₂'
  | mutualUnobservedStep h =>
    exact Same.fold (sameFinite_unobservedL (forallUnobserved_mono h fun _ h =>
      Same.unfold ((forallUnobserved_silent h₂).mp h)))

theorem Same.branchL_inv {m₁ : CoFree E A} {m₂ : CoFree E B} {c : E.BrOp}
    {k : E.BrResp c → CoFree E A} (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .branch c k)
    (r : E.BrResp c) : Same Ret (k r) m₂ := by
  replace h := Same.unfold h
  induction h generalizing k with
  | ret _ _ h₁' => rw [h₁] at h₁'; cases h₁'
  | impure _ h₁' => rw [h₁] at h₁'; cases h₁'
  | silentL h₁' => rw [h₁] at h₁'; cases h₁'
  | silentR h₂ _ ih => exact Same.silentR h₂ (ih h₁)
  | branchL _ h₁' h => rw [h₁] at h₁'; cases h₁'; exact Same.fold (h r)
  | branchR c h₂ _ ih => exact Same.branchR c h₂ fun r' => ih r' h₁
  | mutualUnobservedStep h =>
    rw [forallUnobserved_branch h₁] at h
    exact Same.fold (sameFinite_unobservedR (forallUnobserved_mono (h r) fun _ => Same.unfold))

theorem Same.branchR_inv {m₁ : CoFree E A} {m₂ : CoFree E B} {c : E.BrOp}
    {k : E.BrResp c → CoFree E B} (h : Same Ret m₁ m₂) (h₂ : m₂.observe = .branch c k)
    (r : E.BrResp c) : Same Ret m₁ (k r) := by
  replace h := Same.unfold h
  induction h generalizing k with
  | ret _ _ _ h₂' => rw [h₂] at h₂'; cases h₂'
  | impure _ _ h₂' => rw [h₂] at h₂'; cases h₂'
  | silentL h₁ _ ih => exact Same.silentL h₁ (ih h₂)
  | silentR h₂' => rw [h₂] at h₂'; cases h₂'
  | branchL c h₁ _ ih => exact Same.branchL c h₁ fun r' => ih r' h₂
  | branchR _ h₂' h => rw [h₂] at h₂'; cases h₂'; exact Same.fold (h r)
  | mutualUnobservedStep h =>
    exact Same.fold (sameFinite_unobservedL (forallUnobserved_mono h fun _ h =>
      Same.unfold ((forallUnobserved_branch h₂).mp h r)))

/-- After an unobserved step on the left, the successors are still related. -/
theorem Same.unobservedL_inv {m₁ : CoFree E A} {m₂ : CoFree E B} (h : Same Ret m₁ m₂)
    (hu : ForallUnobserved m₁ fun _ => True) : ForallUnobserved m₁ fun n => Same Ret n m₂ := by
  unfold ForallUnobserved at hu ⊢
  split at hu
  · rename_i h₁; exact Same.silentL_inv h h₁
  · rename_i h₁; exact Same.branchL_inv h h₁
  · exact hu.elim

theorem Same.unobservedR_inv {m₁ : CoFree E A} {m₂ : CoFree E B} (h : Same Ret m₁ m₂)
    (hu : ForallUnobserved m₂ fun _ => True) : ForallUnobserved m₂ fun n => Same Ret m₁ n := by
  unfold ForallUnobserved at hu ⊢
  split at hu
  · rename_i h₂; exact Same.silentR_inv h h₂
  · rename_i h₂; exact Same.branchR_inv h h₂
  · exact hu.elim

theorem Same.ret_inv {m₁ : CoFree E A} {m₂ : CoFree E B} {a : A} {b : B}
    (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .pure a) (h₂ : m₂.observe = .pure b) : Ret a b := by
  cases Same.unfold h with
  | ret _ _ h₁' h₂' hab => rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'; exact hab
  | impure _ h₁' => rw [h₁] at h₁'; cases h₁'
  | silentL h₁' => rw [h₁] at h₁'; cases h₁'
  | silentR h₂' => rw [h₂] at h₂'; cases h₂'
  | branchL _ h₁' => rw [h₁] at h₁'; cases h₁'
  | branchR _ h₂' => rw [h₂] at h₂'; cases h₂'
  | mutualUnobservedStep h => exact (not_forallUnobserved_pure h₁ h).elim

/-- Two related visible operations are the same operation. -/
theorem Same.impure_inv {m₁ : CoFree E A} {m₂ : CoFree E B}
    {op₁ op₂ : E.Op} {k₁ : E.Resp op₁ → CoFree E A} {k₂ : E.Resp op₂ → CoFree E B}
    (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .impure op₁ k₁)
    (h₂ : m₂.observe = .impure op₂ k₂) : op₁ = op₂ := by
  cases Same.unfold h with
  | ret _ _ h₁' => rw [h₁] at h₁'; cases h₁'
  | impure _ h₁' h₂' => rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'; rfl
  | silentL h₁' => rw [h₁] at h₁'; cases h₁'
  | silentR h₂' => rw [h₂] at h₂'; cases h₂'
  | branchL _ h₁' => rw [h₁] at h₁'; cases h₁'
  | branchR _ h₂' => rw [h₂] at h₂'; cases h₂'
  | mutualUnobservedStep h => exact (not_forallUnobserved_impure h₁ h).elim

/-- Related machines performing the same operation stay related for every response. -/
theorem Same.impure_inv_resp {m₁ : CoFree E A} {m₂ : CoFree E B}
    {op : E.Op} {k₁ : E.Resp op → CoFree E A} {k₂ : E.Resp op → CoFree E B}
    (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .impure op k₁)
    (h₂ : m₂.observe = .impure op k₂) (r : E.Resp op) : Same Ret (k₁ r) (k₂ r) := by
  cases Same.unfold h with
  | ret _ _ h₁' => rw [h₁] at h₁'; cases h₁'
  | impure _ h₁' h₂' hk => rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'; exact hk r
  | silentL h₁' => rw [h₁] at h₁'; cases h₁'
  | silentR h₂' => rw [h₂] at h₂'; cases h₂'
  | branchL _ h₁' => rw [h₁] at h₁'; cases h₁'
  | branchR _ h₂' => rw [h₂] at h₂'; cases h₂'
  | mutualUnobservedStep h => exact (not_forallUnobserved_impure h₁ h).elim

end Inversion

/-! ## Symmetry, monotonicity, reflexivity without branches -/

theorem Same.symm {Ret : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same Ret m₁ m₂) : Same (fun b a => Ret a b) m₂ m₁ := by
  refine ⟨fun y x => Same Ret x y, h, fun y x hxy => ?_⟩
  replace hxy := Same.unfold hxy
  induction hxy with
  | ret a b h₁ h₂ hab => exact .ret b a h₂ h₁ hab
  | impure op h₁ h₂ hk => exact .impure op h₂ h₁ hk
  | silentL h₁ _ ih => exact .silentR h₁ ih
  | silentR h₂ _ ih => exact .silentL h₂ ih
  | branchL c h₁ _ ih => exact .branchR c h₁ ih
  | branchR c h₂ _ ih => exact .branchL c h₂ ih
  | mutualUnobservedStep h => exact .mutualUnobservedStep (forallUnobserved_swap h)

theorem Same.mono {Ret Ret' : A → B → Prop} (hRet : ∀ a b, Ret a b → Ret' a b)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : Same Ret m₁ m₂) :
    Same Ret' m₁ m₂ := by
  refine ⟨Same Ret, h, fun x y hxy => ?_⟩
  replace hxy := Same.unfold hxy
  induction hxy with
  | ret a b h₁ h₂ hab => exact .ret a b h₁ h₂ (hRet _ _ hab)
  | impure op h₁ h₂ hk => exact .impure op h₁ h₂ hk
  | silentL h₁ _ ih => exact .silentL h₁ ih
  | silentR h₂ _ ih => exact .silentR h₂ ih
  | branchL c h₁ _ ih => exact .branchL c h₁ ih
  | branchR c h₂ _ ih => exact .branchR c h₂ ih
  | mutualUnobservedStep h => exact .mutualUnobservedStep h

theorem Same.refl {Ret : A → A → Prop}
    (hbr : E.BrOp → False) (hRet : ∀ a, Ret a a) (m : CoFree E A) : Same Ret m m := by
  refine ⟨Eq, rfl, ?_⟩
  rintro x _ rfl
  cases h : x.observe with
  | pure a => exact .ret a a h h (hRet a)
  | silent n =>
    exact .mutualUnobservedStep ((forallUnobserved_silent h).mpr
      ((forallUnobserved_silent h).mpr rfl))
  | impure op k => exact .impure op h h fun _ => rfl
  | branch c _ => exact (hbr c).elim

/-! ## Transitivity

A step both outer machines take together may correspond to several unobserved steps of the
middle machine. `trans_unobserved` consumes those by induction; once the middle machine shows
something other than an unobserved step, `trans_visible` lines the outer machines up. Every
branch has a response, so the middle machine can always be advanced through its unobserved
steps. -/

section Trans

variable {RA : A → B → Prop} {RB : B → C → Prop}

theorem trans_ret {x : CoFree E A} {y : CoFree E B} {z : CoFree E C} {a : A} {b : B}
    (hx : x.observe = .pure a) (hy : y.observe = .pure b) (hab : RA a b)
    (h₂ : SameFinite RB (Same RB) y z) :
    SameFinite (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same RA x y ∧ Same RB y z) x z := by
  induction h₂ with
  | ret _ c hy' hz hbc => rw [hy] at hy'; cases hy'; exact .ret a c hx hz ⟨_, hab, hbc⟩
  | impure _ hy' => rw [hy] at hy'; cases hy'
  | silentL hy' => rw [hy] at hy'; cases hy'
  | silentR hz _ ih => exact .silentR hz (ih hy)
  | branchL _ hy' => rw [hy] at hy'; cases hy'
  | branchR c hz _ ih => exact .branchR c hz fun r => ih r hy
  | mutualUnobservedStep h => exact (not_forallUnobserved_pure hy h).elim

theorem trans_impure {x : CoFree E A} {y : CoFree E B} {z : CoFree E C} {op : E.Op}
    {k₁ : E.Resp op → CoFree E A} {k₂ : E.Resp op → CoFree E B}
    (hx : x.observe = .impure op k₁) (hy : y.observe = .impure op k₂)
    (hk : ∀ r, Same RA (k₁ r) (k₂ r))
    (h₂ : SameFinite RB (Same RB) y z) :
    SameFinite (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same RA x y ∧ Same RB y z) x z := by
  induction h₂ with
  | ret _ _ hy' => rw [hy] at hy'; cases hy'
  | impure _ hy' hz hk' =>
    rw [hy] at hy'; cases hy'
    exact .impure op hx hz fun r => ⟨_, hk r, hk' r⟩
  | silentL hy' => rw [hy] at hy'; cases hy'
  | silentR hz _ ih => exact .silentR hz (ih hy)
  | branchL _ hy' => rw [hy] at hy'; cases hy'
  | branchR c hz _ ih => exact .branchR c hz fun r => ih r hy
  | mutualUnobservedStep h => exact (not_forallUnobserved_impure hy h).elim

theorem trans_visible {x : CoFree E A} {y : CoFree E B} {z : CoFree E C}
    (h₁ : SameFinite RA (Same RA) x y) :
    ¬ForallUnobserved y (fun _ => True) → SameFinite RB (Same RB) y z →
    SameFinite (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same RA x y ∧ Same RB y z) x z := by
  induction h₁ with
  | ret _ _ hx hy hab => intro _ h₂; exact trans_ret hx hy hab h₂
  | impure op hx hy hk => intro _ h₂; exact trans_impure hx hy hk h₂
  | silentL hx _ ih => intro hy h₂; exact .silentL hx (ih hy h₂)
  | silentR hy => intro hu; exact (hu ((forallUnobserved_silent hy).mpr trivial)).elim
  | branchL c hx _ ih => intro hy h₂; exact .branchL c hx fun r => ih r hy h₂
  | branchR _ hy => intro hu; exact (hu ((forallUnobserved_branch hy).mpr fun _ => trivial)).elim
  | mutualUnobservedStep h =>
    intro hu
    obtain ⟨_, h, _⟩ := forallUnobserved_exists h h
    exact (hu (forallUnobserved_mono h fun _ _ => trivial)).elim

/-- The middle machine `y`, at an unobserved step, has reached `y'` (one of its successors);
if `y'` is again unobserved, keep going, else line up with `trans_visible`. -/
theorem trans_unobserved_next {x : CoFree E A} {y' : CoFree E B} {z : CoFree E C}
    (H : ForallUnobserved x fun x' => Same RA x' y')
    (h₂ : SameFinite RB (Same RB) y' z)
    (ih : ForallUnobserved y' (fun _ => True) →
      (ForallUnobserved x fun x' => ForallUnobserved y' (Same RA x')) →
      SameFinite (fun a c => ∃ b, RA a b ∧ RB b c)
        (fun x z => ∃ y, Same RA x y ∧ Same RB y z) x z) :
    SameFinite (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same RA x y ∧ Same RB y z) x z := by
  by_cases hu : ForallUnobserved y' fun _ => True
  · exact ih hu (forallUnobserved_mono H fun _ h => Same.unobservedR_inv h hu)
  · exact sameFinite_unobservedL (forallUnobserved_mono H fun _ h =>
      trans_visible (Same.unfold h) hu h₂)

theorem trans_unobserved {x : CoFree E A} {y : CoFree E B} {z : CoFree E C}
    (h₂ : SameFinite RB (Same RB) y z) :
    ForallUnobserved y (fun _ => True) →
    (ForallUnobserved x fun x' => ForallUnobserved y (Same RA x')) →
    SameFinite (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same RA x y ∧ Same RB y z) x z := by
  induction h₂ with
  | ret _ _ hy => intro hu; exact (not_forallUnobserved_pure hy hu).elim
  | impure _ hy => intro hu; exact (not_forallUnobserved_impure hy hu).elim
  | silentL hy h ih =>
    intro _ H
    exact trans_unobserved_next (forallUnobserved_mono H fun _ h =>
      (forallUnobserved_silent hy).mp h) h ih
  | silentR hz _ ih => intro hu H; exact .silentR hz (ih hu H)
  | branchL c hy h ih =>
    intro _ H
    obtain ⟨r⟩ := E.brResp_nonempty c
    exact trans_unobserved_next (forallUnobserved_mono H fun _ h =>
      (forallUnobserved_branch hy).mp h r) (h r) (ih r)
  | branchR c hz _ ih => intro hu H; exact .branchR c hz fun r => ih r hu H
  | mutualUnobservedStep h =>
    intro _ H
    refine .mutualUnobservedStep (forallUnobserved_mono H fun x' hx' => ?_)
    obtain ⟨y', h₁, h₂⟩ := forallUnobserved_exists hx' h
    exact forallUnobserved_mono h₂ fun _ h₃ => ⟨y', h₁, h₃⟩

theorem trans_step {x : CoFree E A} {y : CoFree E B} {z : CoFree E C}
    (h₁ : SameFinite RA (Same RA) x y) :
    Same RB y z →
    SameFinite (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same RA x y ∧ Same RB y z) x z := by
  induction h₁ with
  | ret _ _ hx hy hab => intro h₂; exact trans_ret hx hy hab (Same.unfold h₂)
  | impure op hx hy hk => intro h₂; exact trans_impure hx hy hk (Same.unfold h₂)
  | silentL hx _ ih => intro h₂; exact .silentL hx (ih h₂)
  | silentR hy _ ih => intro h₂; exact ih (Same.silentL_inv h₂ hy)
  | branchL c hx _ ih => intro h₂; exact .branchL c hx fun r => ih r h₂
  | branchR c hy _ ih =>
    intro h₂
    obtain ⟨r⟩ := E.brResp_nonempty c
    exact ih r (Same.branchL_inv h₂ hy r)
  | mutualUnobservedStep h =>
    intro h₂
    obtain ⟨_, h', _⟩ := forallUnobserved_exists h h
    exact trans_unobserved (Same.unfold h₂) (forallUnobserved_mono h' fun _ _ => trivial) h

theorem Same.trans {x : CoFree E A} {y : CoFree E B} {z : CoFree E C}
    (h₁ : Same RA x y) (h₂ : Same RB y z) :
    Same (fun a c => ∃ b, RA a b ∧ RB b c) x z :=
  ⟨fun x z => ∃ y, Same RA x y ∧ Same RB y z, ⟨_, h₁, h₂⟩,
   fun _ _ ⟨_, h₁, h₂⟩ => trans_step (Same.unfold h₁) h₂⟩

end Trans

/-! ## Determinism -/

theorem Same.deterministic_left {Ret : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same Ret m₁ m₂) : Same (fun a a' => ∃ b, Ret a b ∧ Ret a' b) m₁ m₁ :=
  Same.trans h (Same.symm h)

theorem Same.deterministic_right {Ret : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same Ret m₁ m₂) : Same (fun b b' => ∃ a, Ret a b ∧ Ret a b') m₂ m₂ :=
  Same.trans (Same.symm h) h

theorem Same.symm_eq {m₁ m₂ : CoFree E A} (h : Same Eq m₁ m₂) : Same Eq m₂ m₁ :=
  Same.mono (fun _ _ h => h.symm) (Same.symm h)

theorem Same.trans_eq {m₁ m₂ m₃ : CoFree E A} (h₁ : Same Eq m₁ m₂) (h₂ : Same Eq m₂ m₃) :
    Same Eq m₁ m₃ :=
  Same.mono (fun _ _ ⟨_, h₁, h₂⟩ => h₁.trans h₂) (Same.trans h₁ h₂)

theorem Deterministic.of_same {m₁ m₂ : CoFree E A} (h : Same Eq m₁ m₂) :
    Deterministic m₁ ∧ Deterministic m₂ :=
  ⟨Same.trans_eq h (Same.symm_eq h), Same.trans_eq (Same.symm_eq h) h⟩

theorem Same.not_of_not_self_left {Ret : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hself : ∀ R : A → A → Prop, ¬Same R m₁ m₁) : ¬Same Ret m₁ m₂ :=
  fun h => hself _ (Same.deterministic_left h)

theorem Same.not_of_not_self_right {Ret : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hself : ∀ R : B → B → Prop, ¬Same R m₂ m₂) : ¬Same Ret m₁ m₂ :=
  fun h => hself _ (Same.deterministic_right h)

/-! ## Bind -/

theorem Same.bind {Ret : A → B → Prop} {Ret' : C → D → Prop} {m₁ : CoFree E A}
    {m₂ : CoFree E B} {f : A → CoFree E C} {g : B → CoFree E D} (h : Same Ret m₁ m₂)
    (hfg : ∀ a b, Ret a b → Same Ret' (f a) (g b)) :
    Same Ret' (m₁.bind f) (m₂.bind g) := by
  refine Same.coind (fun x y => ∃ m₁ m₂, Same Ret m₁ m₂ ∧ x = m₁.bind f ∧
    y = m₂.bind g) ?_ ⟨m₁, m₂, h, rfl, rfl⟩
  rintro _ _ ⟨m₁, m₂, h, rfl, rfl⟩
  replace h := Same.unfold h
  induction h with
  | ret a b h₁ h₂ hab =>
    exact SameFinite.congr (SameFinite.mono (fun _ _ => .inr) (Same.unfold (hfg _ _ hab)))
      (by rw [observe_bind, h₁]; rfl) (by rw [observe_bind, h₂]; rfl)
  | impure op h₁ h₂ hk =>
    exact .impure op (by rw [observe_bind, h₁]; rfl) (by rw [observe_bind, h₂]; rfl)
      fun r => .inl ⟨_, _, hk r, rfl, rfl⟩
  | silentL h₁ _ ih => exact .silentL (by rw [observe_bind, h₁]; rfl) ih
  | silentR h₂ _ ih => exact .silentR (by rw [observe_bind, h₂]; rfl) ih
  | branchL c h₁ _ ih => exact .branchL c (by rw [observe_bind, h₁]; rfl) ih
  | branchR c h₂ _ ih => exact .branchR c (by rw [observe_bind, h₂]; rfl) ih
  | mutualUnobservedStep h =>
    exact .mutualUnobservedStep (forallUnobserved_bind (forallUnobserved_mono h fun n₁ h =>
      forallUnobserved_bind (forallUnobserved_mono h fun n₂ h => .inl ⟨n₁, n₂, h, rfl, rfl⟩)))

/-! ## Sanity checks of the definition -/

theorem spin_observe : (spin : CoFree E A).observe = .silent spin := rfl

theorem spin_relates_to_self : ∀ {E A B Ret}, Same Ret (spin (E := E) (A := A)) (spin (E := E) (A := B)) := by
  intro E A B Ret
  unfold Same
  exact ⟨fun m₁ m₂ => m₁ = spin ∧ m₂ = spin, by {
    simp
    exact SameFinite.mutualUnobservedStep (by
      unfold ForallUnobserved spin observe Step.map CoFree.next CoFree.startAt
      simp
    )
  }⟩

section Sanity

variable {Ret : A → B → Prop}

/-- A machine that only runs silently is related to no machine that returns. -/
theorem Same.not_spin_pure {b : B} : ¬Same Ret (spin : CoFree E A) (CoFree.pure b) := by
  intro h
  replace h := Same.unfold h
  generalize hs : (spin : CoFree E A) = s at h
  generalize hp : (CoFree.pure b : CoFree E B) = p at h
  induction h with
  | ret _ _ h₁ => subst hs; cases h₁
  | impure _ h₁ => subst hs; cases h₁
  | silentL h₁ _ ih => subst hs; cases h₁; exact ih rfl hp
  | silentR h₂ => subst hp; cases h₂
  | branchL _ h₁ => subst hs; cases h₁
  | branchR _ h₂ => subst hp; cases h₂
  | mutualUnobservedStep h =>
    subst hs hp
    exact not_forallUnobserved_pure (observe_pure b) ((forallUnobserved_silent spin_observe).mp h)

/-- Nor to one that performs an operation. -/
theorem Same.not_spin_impure {op : E.Op} {k : E.Resp op → CoFree E B} :
    ¬Same Ret (spin : CoFree E A) (CoFree.impure op k) := by
  intro h
  replace h := Same.unfold h
  generalize hs : (spin : CoFree E A) = s at h
  generalize hp : CoFree.impure op k = p at h
  induction h with
  | ret _ _ h₁ => subst hs; cases h₁
  | impure _ h₁ => subst hs; cases h₁
  | silentL h₁ _ ih => subst hs; cases h₁; exact ih rfl hp
  | silentR h₂ => subst hp; cases h₂
  | branchL _ h₁ => subst hs; cases h₁
  | branchR _ h₂ => subst hp; cases h₂
  | mutualUnobservedStep h =>
    subst hs hp
    exact not_forallUnobserved_impure (observe_impure op k)
      ((forallUnobserved_silent spin_observe).mp h)

theorem Same.pure_iff {a : A} {b : B} :
    Same Ret (CoFree.pure a : CoFree E A) (CoFree.pure b) ↔ Ret a b :=
  ⟨fun h => Same.ret_inv h rfl rfl, Same.ret rfl rfl⟩

/-- A silent step on the left is invisible. -/
theorem Same.silent_iff_left {m₁ : CoFree E A} {m₂ : CoFree E B} :
    Same Ret (CoFree.silent m₁) m₂ ↔ Same Ret m₁ m₂ :=
  ⟨fun h => Same.silentL_inv h rfl, Same.silentL rfl⟩

theorem Same.silent_iff_right {m₁ : CoFree E A} {m₂ : CoFree E B} :
    Same Ret m₁ (CoFree.silent m₂) ↔ Same Ret m₁ m₂ :=
  ⟨fun h => Same.silentR_inv h rfl, Same.silentR rfl⟩

theorem Same.impure_iff {op : E.Op} {k₁ : E.Resp op → CoFree E A}
    {k₂ : E.Resp op → CoFree E B} :
    Same Ret (CoFree.impure op k₁) (CoFree.impure op k₂) ↔ ∀ r, Same Ret (k₁ r) (k₂ r) :=
  ⟨fun h => Same.impure_inv_resp h rfl rfl, Same.impure op rfl rfl⟩

theorem Same.impure_ne {op₁ op₂ : E.Op} {k₁ : E.Resp op₁ → CoFree E A}
    {k₂ : E.Resp op₂ → CoFree E B} (hne : op₁ ≠ op₂) :
    ¬Same Ret (CoFree.impure op₁ k₁) (CoFree.impure op₂ k₂) :=
  fun h => hne (Same.impure_inv h rfl rfl)

/-- An operation with no response ends the run (undefined behavior is one): it relates to itself,
whatever the continuations. -/
theorem Same.terminal {op : E.Op} (hop : E.Resp op → False) (k₁ : E.Resp op → CoFree E A)
    (k₂ : E.Resp op → CoFree E B) : Same Ret (CoFree.impure op k₁) (CoFree.impure op k₂) :=
  Same.impure op rfl rfl fun r => (hop r).elim

/-- Two branches are related iff every pair of responses is. -/
theorem Same.branch_iff {c₁ c₂ : E.BrOp} {k₁ : E.BrResp c₁ → CoFree E A}
    {k₂ : E.BrResp c₂ → CoFree E B} :
    Same Ret (CoFree.branch c₁ k₁) (CoFree.branch c₂ k₂) ↔
      ∀ r₁ r₂, Same Ret (k₁ r₁) (k₂ r₂) :=
  ⟨fun h r₁ r₂ => Same.branchR_inv (Same.branchL_inv h rfl r₁) rfl r₂, Same.branch rfl rfl⟩

/-- A branch on the left is related iff every response is. -/
theorem Same.branch_iff_left {c : E.BrOp} {k : E.BrResp c → CoFree E A} {m₂ : CoFree E B} :
    Same Ret (CoFree.branch c k) m₂ ↔ ∀ r, Same Ret (k r) m₂ :=
  ⟨fun h r => Same.branchL_inv h rfl r, Same.branchL c rfl⟩

/-- A branch that ignores its response is invisible. -/
theorem Same.branch_const {c : E.BrOp} {m₁ : CoFree E A} {m₂ : CoFree E B} :
    Same Ret (CoFree.branch c fun _ => m₁) m₂ ↔ Same Ret m₁ m₂ :=
  ⟨fun h => let ⟨r⟩ := E.brResp_nonempty c; Same.branchL_inv h rfl r,
   fun h => Same.branchL c rfl fun _ => h⟩

/-- A machine whose visible behavior depends on a branch is not related to itself. -/
theorem Same.not_refl_of_branch {Ret : A → A → Prop} {m : CoFree E A} {c : E.BrOp}
    {k : E.BrResp c → CoFree E A} (h : m.observe = .branch c k) {r₁ r₂ : E.BrResp c}
    (hne : ¬Same Ret (k r₁) (k r₂)) : ¬Same Ret m m :=
  fun hm => hne (Same.branchR_inv (Same.branchL_inv hm h r₁) h r₂)

/-- Divergence absorbs branches: branching into machines that all diverge is the same as
diverging. -/
theorem Same.spin_branch_spin {c : E.BrOp} :
    Same Ret (spin : CoFree E A) (CoFree.branch c fun _ => (spin : CoFree E B)) :=
  Same.branchR c rfl fun _ => spin_relates_to_self

end Sanity

end CoFree.Proofs
