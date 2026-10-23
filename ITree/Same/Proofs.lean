import ITree.Same
import ITree.Machine.Theorems

universe u

namespace CoFree.Proofs

variable {E : Effect.{u}} {A B C D : Type u} {hidden ub : E.Op → Prop}

/-! ## Silent steps -/

theorem next_congr {m m' n : CoFree E A} (he : m.observe = m'.observe) :
    Next hidden m n → Next hidden m' n := by
  unfold Next; rw [he]; exact id

theorem silent_congr {m m' : CoFree E A} (he : m.observe = m'.observe) :
    Silent hidden m → Silent hidden m'
  | .inl ⟨n, hn⟩ => .inl ⟨n, next_congr he hn⟩
  | .inr ⟨c, k, h⟩ => .inr ⟨c, k, he ▸ h⟩

theorem not_silent_pure {m : CoFree E A} {a : A} (h : m.observe = .pure a) :
    ¬Silent hidden m := by
  rintro (⟨n, hn | ⟨_, _, _, hn, _⟩ | ⟨_, _, hn, _⟩⟩ | ⟨_, _, hn⟩) <;> rw [h] at hn <;> cases hn

theorem not_silent_impure {m : CoFree E A} {op : E.Op} {k : E.Resp op → CoFree E A}
    (h : m.observe = .impure op k) (hop : ¬hidden op) : ¬Silent hidden m := by
  rintro (⟨n, hn | ⟨op', hop', k', hn, _⟩ | ⟨_, _, hn, _⟩⟩ | ⟨_, _, hn⟩) <;> rw [h] at hn <;>
    cases hn
  exact hop hop'

theorem next_silent_iff {m n n' : CoFree E A} (h : m.observe = .silent n) :
    Next hidden m n' ↔ n' = n := by
  constructor
  · rintro (hn | ⟨_, _, _, hn, _⟩ | ⟨_, _, hn, _⟩) <;> rw [h] at hn <;> cases hn
    rfl
  · rintro rfl; exact .inl h

theorem next_hidden_iff {m n : CoFree E A} {op : E.Op} {k : E.Resp op → CoFree E A}
    (h : m.observe = .impure op k) (hop : hidden op) : Next hidden m n ↔ ∃ r, k r = n := by
  constructor
  · rintro (hn | ⟨_, _, _, hn, r, rfl⟩ | ⟨_, _, hn, _⟩) <;> rw [h] at hn <;> cases hn
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩; exact .inr (.inl ⟨op, hop, k, h, r, rfl⟩)

theorem next_br_iff {m n : CoFree E A} {c : E.BrOp} {k : E.BrResp c → CoFree E A}
    (h : m.observe = .br c k) : Next hidden m n ↔ ∃ r, k r = n := by
  constructor
  · rintro (hn | ⟨_, _, _, hn, _⟩ | ⟨_, _, hn, r, rfl⟩) <;> rw [h] at hn <;> cases hn
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩; exact .inr (.inr ⟨c, k, h, r, rfl⟩)

theorem silent_of_silent {m n : CoFree E A} (h : m.observe = .silent n) : Silent hidden m :=
  .inl ⟨n, .inl h⟩

theorem silent_of_hidden {m : CoFree E A} {op : E.Op} {k : E.Resp op → CoFree E A}
    (h : m.observe = .impure op k) (hop : hidden op) (r : E.Resp op) : Silent hidden m :=
  .inl ⟨k r, .inr (.inl ⟨op, hop, k, h, r, rfl⟩)⟩

theorem silent_of_br {m : CoFree E A} {c : E.BrOp} {k : E.BrResp c → CoFree E A}
    (h : m.observe = .br c k) : Silent hidden m :=
  .inr ⟨c, k, h⟩

/-- When every branch has a response, a silent step has somewhere to go. -/
theorem exists_next (hbr : ∀ c : E.BrOp, Nonempty (E.BrResp c)) {m : CoFree E A} :
    Silent hidden m → ∃ n, Next hidden m n
  | .inl h => h
  | .inr ⟨c, k, h⟩ => let ⟨r⟩ := hbr c; ⟨k r, .inr (.inr ⟨c, k, h, r, rfl⟩)⟩

/-! ## The fixed point -/

theorem SameF.mono {RR : A → B → Prop} {R R' : CoFree E A → CoFree E B → Prop}
    (hR : ∀ x y, R x y → R' x y) {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : SameF hidden ub RR R m₁ m₂) : SameF hidden ub RR R' m₁ m₂ := by
  induction h with
  | silent hs₁ hs₂ h => exact .silent hs₁ hs₂ fun n₁ n₂ h₁ h₂ => hR _ _ (h n₁ n₂ h₁ h₂)
  | impure op h₁ h₂ hop hk => exact .impure op h₁ h₂ hop fun r => hR _ _ (hk r)
  | ret h₁ h₂ hab => exact .ret h₁ h₂ hab
  | ub op₁ op₂ h₁ h₂ hub₁ hub₂ hop₁ hop₂ => exact .ub op₁ op₂ h₁ h₂ hub₁ hub₂ hop₁ hop₂
  | silentL hs _ ih => exact .silentL hs ih
  | silentR hs _ ih => exact .silentR hs ih

theorem SameF.congr {RR : A → B → Prop} {R : CoFree E A → CoFree E B → Prop}
    {m₁ m₁' : CoFree E A} {m₂ m₂' : CoFree E B} (h : SameF hidden ub RR R m₁ m₂)
    (he₁ : m₁.observe = m₁'.observe) (he₂ : m₂.observe = m₂'.observe) :
    SameF hidden ub RR R m₁' m₂' := by
  induction h generalizing m₁' m₂' with
  | silent hs₁ hs₂ h =>
    exact .silent (silent_congr he₁ hs₁) (silent_congr he₂ hs₂) fun n₁ n₂ h₁ h₂ =>
      h n₁ n₂ (next_congr he₁.symm h₁) (next_congr he₂.symm h₂)
  | impure op h₁ h₂ hop hk => exact .impure op (he₁ ▸ h₁) (he₂ ▸ h₂) hop hk
  | ret h₁ h₂ hab => exact .ret (he₁ ▸ h₁) (he₂ ▸ h₂) hab
  | ub op₁ op₂ h₁ h₂ hub₁ hub₂ hop₁ hop₂ =>
    exact .ub op₁ op₂ (he₁ ▸ h₁) (he₂ ▸ h₂) hub₁ hub₂ hop₁ hop₂
  | silentL hs _ ih =>
    exact .silentL (silent_congr he₁ hs) fun n hn => ih n (next_congr he₁.symm hn) rfl he₂
  | silentR hs _ ih =>
    exact .silentR (silent_congr he₂ hs) fun n hn => ih n (next_congr he₂.symm hn) he₁ rfl

theorem Same.unfold {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B} :
    Same hidden ub RR m₁ m₂ → SameF hidden ub RR (Same hidden ub RR) m₁ m₂
  | ⟨R, hR, h⟩ => SameF.mono (fun _ _ hxy => ⟨R, hR, hxy⟩) (hR _ _ h)

theorem Same.fold {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : SameF hidden ub RR (Same hidden ub RR) m₁ m₂) : Same hidden ub RR m₁ m₂ :=
  ⟨SameF hidden ub RR (Same hidden ub RR), fun _ _ h => SameF.mono (fun _ _ => Same.unfold) h, h⟩

/-- Coinduction up to `Same`: `R` may step to pairs already known to be related. -/
theorem Same.coind {RR : A → B → Prop} (R : CoFree E A → CoFree E B → Prop)
    (hR : ∀ x y, R x y → SameF hidden ub RR (fun x y => R x y ∨ Same hidden ub RR x y) x y)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : R m₁ m₂) : Same hidden ub RR m₁ m₂ := by
  refine ⟨fun x y => R x y ∨ Same hidden ub RR x y, ?_, .inl h⟩
  rintro x y (hxy | hxy)
  · exact hR x y hxy
  · exact SameF.mono (fun _ _ => .inr) (Same.unfold hxy)

/-- Coinduction up to finitely many layers of `SameF` and up to `Same`. -/
theorem Same.coind_steps {RR : A → B → Prop} (R : CoFree E A → CoFree E B → Prop)
    (hR : ∀ x y, R x y → SameF hidden ub RR (SameSteps hidden ub RR R) x y)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : R m₁ m₂) : Same hidden ub RR m₁ m₂ := by
  refine ⟨SameSteps hidden ub RR R, fun x y hxy => ?_, .recur h⟩
  cases hxy with
  | done h => exact SameF.mono (fun _ _ => .done) (Same.unfold h)
  | step h => exact h
  | recur h => exact hR x y h

theorem Same.congr {RR : A → B → Prop} {m₁ m₁' : CoFree E A} {m₂ m₂' : CoFree E B}
    (h : Same hidden ub RR m₁ m₂) (he₁ : m₁.observe = m₁'.observe)
    (he₂ : m₂.observe = m₂'.observe) : Same hidden ub RR m₁' m₂' :=
  Same.fold (SameF.congr (Same.unfold h) he₁ he₂)

/-! ## Constructors -/

theorem Same.silent {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs₁ : Silent hidden m₁) (hs₂ : Silent hidden m₂)
    (h : ∀ n₁ n₂, Next hidden m₁ n₁ → Next hidden m₂ n₂ → Same hidden ub RR n₁ n₂) :
    Same hidden ub RR m₁ m₂ :=
  Same.fold (.silent hs₁ hs₂ h)

theorem Same.impure {RR : A → B → Prop} (op : E.Op) (hop : ¬hidden op)
    {k₁ : E.Resp op → CoFree E A} {k₂ : E.Resp op → CoFree E B}
    (h : ∀ r, Same hidden ub RR (k₁ r) (k₂ r)) :
    Same hidden ub RR (CoFree.impure op k₁) (CoFree.impure op k₂) :=
  Same.fold (.impure op rfl rfl hop h)

theorem Same.ret {RR : A → B → Prop} {a : A} {b : B} (h : RR a b) :
    Same hidden ub RR (CoFree.pure a : CoFree E A) (CoFree.pure b) :=
  Same.fold (.ret rfl rfl h)

theorem Same.undefined {RR : A → B → Prop} (op₁ op₂ : E.Op) (hub₁ : ub op₁) (hub₂ : ub op₂)
    (hop₁ : ¬hidden op₁) (hop₂ : ¬hidden op₂)
    (k₁ : E.Resp op₁ → CoFree E A) (k₂ : E.Resp op₂ → CoFree E B) :
    Same hidden ub RR (CoFree.impure op₁ k₁) (CoFree.impure op₂ k₂) :=
  Same.fold (.ub op₁ op₂ rfl rfl hub₁ hub₂ hop₁ hop₂)

theorem Same.silentL {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs : Silent hidden m₁) (h : ∀ n, Next hidden m₁ n → Same hidden ub RR n m₂) :
    Same hidden ub RR m₁ m₂ :=
  Same.fold (.silentL hs fun n hn => Same.unfold (h n hn))

theorem Same.silentR {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs : Silent hidden m₂) (h : ∀ n, Next hidden m₂ n → Same hidden ub RR m₁ n) :
    Same hidden ub RR m₁ m₂ :=
  Same.fold (.silentR hs fun n hn => Same.unfold (h n hn))

theorem Same.brL {RR : A → B → Prop} (c : E.BrOp) {k : E.BrResp c → CoFree E A}
    {m₂ : CoFree E B} (h : ∀ r, Same hidden ub RR (k r) m₂) :
    Same hidden ub RR (CoFree.br c k) m₂ :=
  Same.silentL (silent_of_br rfl) fun _ hn => by
    obtain ⟨r, rfl⟩ := (next_br_iff rfl).mp hn
    exact h r

theorem Same.brR {RR : A → B → Prop} {m₁ : CoFree E A} (c : E.BrOp)
    {k : E.BrResp c → CoFree E B} (h : ∀ r, Same hidden ub RR m₁ (k r)) :
    Same hidden ub RR m₁ (CoFree.br c k) :=
  Same.silentR (silent_of_br rfl) fun _ hn => by
    obtain ⟨r, rfl⟩ := (next_br_iff rfl).mp hn
    exact h r

/-! ## Inversion -/

theorem Same.silentL_inv {RR : A → B → Prop} {m₁ n₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same hidden ub RR m₁ m₂) (hn : Next hidden m₁ n₁) : Same hidden ub RR n₁ m₂ := by
  replace h := Same.unfold h
  induction h generalizing n₁ with
  | silent _ hs₂ h => exact Same.silentR hs₂ fun n₂ hn₂ => h _ _ hn hn₂
  | impure op h₁ _ hop => exact (not_silent_impure h₁ hop (.inl ⟨_, hn⟩)).elim
  | ret h₁ => exact (not_silent_pure h₁ (.inl ⟨_, hn⟩)).elim
  | ub _ _ h₁ _ _ _ hop₁ => exact (not_silent_impure h₁ hop₁ (.inl ⟨_, hn⟩)).elim
  | silentL _ h => exact Same.fold (h _ hn)
  | silentR hs _ ih => exact Same.fold (.silentR hs fun n₂ hn₂ => Same.unfold (ih n₂ hn₂ hn))

theorem Same.silentR_inv {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ n₂ : CoFree E B}
    (h : Same hidden ub RR m₁ m₂) (hn : Next hidden m₂ n₂) : Same hidden ub RR m₁ n₂ := by
  replace h := Same.unfold h
  induction h generalizing n₂ with
  | silent hs₁ _ h => exact Same.silentL hs₁ fun n₁ hn₁ => h _ _ hn₁ hn
  | impure op _ h₂ hop => exact (not_silent_impure h₂ hop (.inl ⟨_, hn⟩)).elim
  | ret _ h₂ => exact (not_silent_pure h₂ (.inl ⟨_, hn⟩)).elim
  | ub _ _ _ h₂ _ _ _ hop₂ => exact (not_silent_impure h₂ hop₂ (.inl ⟨_, hn⟩)).elim
  | silentL hs _ ih => exact Same.fold (.silentL hs fun n₁ hn₁ => Same.unfold (ih n₁ hn₁ hn))
  | silentR _ h => exact Same.fold (h _ hn)

/-- Two visible, defined operations that are related are the same operation. -/
theorem Same.impure_inv {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    {op₁ op₂ : E.Op} {k₁ : E.Resp op₁ → CoFree E A} {k₂ : E.Resp op₂ → CoFree E B}
    (h : Same hidden ub RR m₁ m₂) (h₁ : m₁.observe = .impure op₁ k₁)
    (h₂ : m₂.observe = .impure op₂ k₂) (hop₁ : ¬hidden op₁) (hop₂ : ¬hidden op₂)
    (hub₁ : ¬ub op₁) : op₁ = op₂ := by
  cases Same.unfold h with
  | silent hs => exact (not_silent_impure h₁ hop₁ hs).elim
  | impure op h₁' h₂' =>
    rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'; rfl
  | ret h₁' => rw [h₁] at h₁'; cases h₁'
  | ub _ _ h₁' _ hub => rw [h₁] at h₁'; cases h₁'; exact (hub₁ hub).elim
  | silentL hs => exact (not_silent_impure h₁ hop₁ hs).elim
  | silentR hs => exact (not_silent_impure h₂ hop₂ hs).elim

/-! ## Symmetry, monotonicity, reflexivity without hidden operations or branches -/

theorem Same.symm {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same hidden ub RR m₁ m₂) : Same hidden ub (fun b a => RR a b) m₂ m₁ := by
  refine ⟨fun y x => Same hidden ub RR x y, fun y x hxy => ?_, h⟩
  replace hxy := Same.unfold hxy
  induction hxy with
  | silent hs₁ hs₂ h => exact .silent hs₂ hs₁ fun n₂ n₁ hn₂ hn₁ => h n₁ n₂ hn₁ hn₂
  | impure op h₁ h₂ hop hk => exact .impure op h₂ h₁ hop hk
  | ret h₁ h₂ hab => exact .ret h₂ h₁ hab
  | ub op₁ op₂ h₁ h₂ hub₁ hub₂ hop₁ hop₂ => exact .ub op₂ op₁ h₂ h₁ hub₂ hub₁ hop₂ hop₁
  | silentL hs _ ih => exact .silentR hs ih
  | silentR hs _ ih => exact .silentL hs ih

theorem Same.mono {RR RR' : A → B → Prop} (hRR : ∀ a b, RR a b → RR' a b)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : Same hidden ub RR m₁ m₂) :
    Same hidden ub RR' m₁ m₂ := by
  refine ⟨Same hidden ub RR, fun x y hxy => ?_, h⟩
  replace hxy := Same.unfold hxy
  induction hxy with
  | silent hs₁ hs₂ h => exact .silent hs₁ hs₂ h
  | impure op h₁ h₂ hop hk => exact .impure op h₁ h₂ hop hk
  | ret h₁ h₂ hab => exact .ret h₁ h₂ (hRR _ _ hab)
  | ub op₁ op₂ h₁ h₂ hub₁ hub₂ hop₁ hop₂ => exact .ub op₁ op₂ h₁ h₂ hub₁ hub₂ hop₁ hop₂
  | silentL hs _ ih => exact .silentL hs ih
  | silentR hs _ ih => exact .silentR hs ih

theorem Same.refl {RR : A → A → Prop} (hhidden : ∀ op, ¬hidden op)
    (hbr : E.BrOp → False) (hRR : ∀ a, RR a a) (m : CoFree E A) : Same hidden ub RR m m := by
  refine ⟨Eq, ?_, rfl⟩
  rintro x _ rfl
  cases h : x.observe with
  | pure a => exact .ret h h (hRR a)
  | silent n =>
    refine .silent (silent_of_silent h) (silent_of_silent h) fun n₁ n₂ h₁ h₂ => ?_
    rw [(next_silent_iff h).mp h₁, (next_silent_iff h).mp h₂]
  | impure op k => exact .impure op h h (hhidden op) fun _ => rfl
  | br c _ => exact (hbr c).elim

/-! ## Transitivity

A step both outer machines take together may correspond to several silent steps of the middle
machine. `trans_silent` consumes those by induction; once the middle machine shows something
other than a silent step, `trans_visible` lines the outer machines up. Hidden operations need
at least one answer to count as silent steps, and branches need one here (`hbr`), exactly so
that the middle machine can be advanced through them. -/

section Trans

variable {RA : A → B → Prop} {RB : B → C → Prop}

theorem trans_ret {x : CoFree E A} {y : CoFree E B} {z : CoFree E C} {a : A} {b : B}
    (hx : x.observe = .pure a) (hy : y.observe = .pure b) (hab : RA a b)
    (h₂ : SameF hidden ub RB (Same hidden ub RB) y z) :
    SameF hidden ub (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same hidden ub RA x y ∧ Same hidden ub RB y z) x z := by
  induction h₂ with
  | silent hs => exact (not_silent_pure hy hs).elim
  | impure _ hy' => rw [hy] at hy'; cases hy'
  | ret hy' hz hbc => rw [hy] at hy'; cases hy'; exact .ret hx hz ⟨_, hab, hbc⟩
  | ub _ _ hy' => rw [hy] at hy'; cases hy'
  | silentL hs => exact (not_silent_pure hy hs).elim
  | silentR hs _ ih => exact .silentR hs fun n hn => ih n hn hy

theorem trans_impure {x : CoFree E A} {y : CoFree E B} {z : CoFree E C} {op : E.Op}
    {k₁ : E.Resp op → CoFree E A} {k₂ : E.Resp op → CoFree E B}
    (hx : x.observe = .impure op k₁) (hy : y.observe = .impure op k₂) (hop : ¬hidden op)
    (hk : ∀ r, Same hidden ub RA (k₁ r) (k₂ r))
    (h₂ : SameF hidden ub RB (Same hidden ub RB) y z) :
    SameF hidden ub (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same hidden ub RA x y ∧ Same hidden ub RB y z) x z := by
  induction h₂ with
  | silent hs => exact (not_silent_impure hy hop hs).elim
  | impure op' hy' hz _ hk' =>
    rw [hy] at hy'; cases hy'
    exact .impure op hx hz hop fun r => ⟨_, hk r, hk' r⟩
  | ret hy' => rw [hy] at hy'; cases hy'
  | ub _ op₃ hy' hz hub hub₃ _ hop₃ =>
    rw [hy] at hy'; cases hy'
    exact .ub op op₃ hx hz hub hub₃ hop hop₃
  | silentL hs => exact (not_silent_impure hy hop hs).elim
  | silentR hs _ ih => exact .silentR hs fun n hn => ih n hn hy

theorem trans_ub {x : CoFree E A} {y : CoFree E B} {z : CoFree E C} {op₁ op₂ : E.Op}
    {k₁ : E.Resp op₁ → CoFree E A} {k₂ : E.Resp op₂ → CoFree E B}
    (hx : x.observe = .impure op₁ k₁) (hy : y.observe = .impure op₂ k₂)
    (hub₁ : ub op₁) (hub₂ : ub op₂) (hop₁ : ¬hidden op₁) (hop₂ : ¬hidden op₂)
    (h₂ : SameF hidden ub RB (Same hidden ub RB) y z) :
    SameF hidden ub (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same hidden ub RA x y ∧ Same hidden ub RB y z) x z := by
  induction h₂ with
  | silent hs => exact (not_silent_impure hy hop₂ hs).elim
  | impure op hy' hz =>
    rw [hy] at hy'; cases hy'
    exact .ub op₁ op₂ hx hz hub₁ hub₂ hop₁ hop₂
  | ret hy' => rw [hy] at hy'; cases hy'
  | ub _ op₃ _ hz _ hub₃ _ hop₃ => exact .ub op₁ op₃ hx hz hub₁ hub₃ hop₁ hop₃
  | silentL hs => exact (not_silent_impure hy hop₂ hs).elim
  | silentR hs _ ih => exact .silentR hs fun n hn => ih n hn hy

theorem trans_visible {x : CoFree E A} {y : CoFree E B} {z : CoFree E C}
    (h₁ : SameF hidden ub RA (Same hidden ub RA) x y) :
    ¬Silent hidden y → SameF hidden ub RB (Same hidden ub RB) y z →
    SameF hidden ub (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same hidden ub RA x y ∧ Same hidden ub RB y z) x z := by
  induction h₁ with
  | silent _ hs => intro hy; exact (hy hs).elim
  | impure op hx hy hop hk => intro _ h₂; exact trans_impure hx hy hop hk h₂
  | ret hx hy hab => intro _ h₂; exact trans_ret hx hy hab h₂
  | ub _ _ hx hy hub₁ hub₂ hop₁ hop₂ => intro _ h₂; exact trans_ub hx hy hub₁ hub₂ hop₁ hop₂ h₂
  | silentL hs _ ih => intro hy h₂; exact .silentL hs fun n hn => ih n hn hy h₂
  | silentR hs => intro hy; exact (hy hs).elim

theorem trans_silent (hbr : ∀ c : E.BrOp, Nonempty (E.BrResp c))
    {x : CoFree E A} {y : CoFree E B} {z : CoFree E C} (hx : Silent hidden x) (h₂ : SameF hidden ub RB (Same hidden ub RB) y z) :
    Silent hidden y →
    (∀ n₁ n₂, Next hidden x n₁ → Next hidden y n₂ → Same hidden ub RA n₁ n₂) →
    SameF hidden ub (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same hidden ub RA x y ∧ Same hidden ub RB y z) x z := by
  induction h₂ with
  | silent hs₂ hs₃ h =>
    intro _ H
    obtain ⟨n₂, hn₂⟩ := exists_next hbr hs₂
    exact .silent hx hs₃ fun n₁ n₃ hn₁ hn₃ => ⟨n₂, H n₁ n₂ hn₁ hn₂, h n₂ n₃ hn₂ hn₃⟩
  | impure _ hy _ hop => intro hs; exact (not_silent_impure hy hop hs).elim
  | ret hy => intro hs; exact (not_silent_pure hy hs).elim
  | ub _ _ hy _ _ _ hop => intro hs; exact (not_silent_impure hy hop hs).elim
  | silentL hs h ih =>
    intro _ H
    obtain ⟨n₂, hn₂⟩ := exists_next hbr hs
    by_cases hs' : Silent hidden n₂
    · exact ih n₂ hn₂ hs' fun n₁ n₂' hn₁ hn₂' => Same.silentR_inv (H n₁ n₂ hn₁ hn₂) hn₂'
    · exact .silentL hx fun n₁ hn₁ =>
        trans_visible (Same.unfold (H n₁ n₂ hn₁ hn₂)) hs' (h n₂ hn₂)
  | silentR hs _ ih => intro hsy H; exact .silentR hs fun n hn => ih n hn hsy H

theorem trans_step (hbr : ∀ c : E.BrOp, Nonempty (E.BrResp c))
    {x : CoFree E A} {y : CoFree E B} {z : CoFree E C} (h₁ : SameF hidden ub RA (Same hidden ub RA) x y) :
    Same hidden ub RB y z →
    SameF hidden ub (fun a c => ∃ b, RA a b ∧ RB b c)
      (fun x z => ∃ y, Same hidden ub RA x y ∧ Same hidden ub RB y z) x z := by
  induction h₁ with
  | silent hs₁ hs₂ h => intro h₂; exact trans_silent hbr hs₁ (Same.unfold h₂) hs₂ h
  | impure op hx hy hop hk => intro h₂; exact trans_impure hx hy hop hk (Same.unfold h₂)
  | ret hx hy hab => intro h₂; exact trans_ret hx hy hab (Same.unfold h₂)
  | ub _ _ hx hy hub₁ hub₂ hop₁ hop₂ =>
    intro h₂; exact trans_ub hx hy hub₁ hub₂ hop₁ hop₂ (Same.unfold h₂)
  | silentL hs _ ih => intro h₂; exact .silentL hs fun n hn => ih n hn h₂
  | silentR hs _ ih =>
    intro h₂
    obtain ⟨n, hn⟩ := exists_next hbr hs
    exact ih n hn (Same.silentL_inv h₂ hn)

theorem Same.trans (hbr : ∀ c : E.BrOp, Nonempty (E.BrResp c))
    {x : CoFree E A} {y : CoFree E B} {z : CoFree E C}
    (h₁ : Same hidden ub RA x y) (h₂ : Same hidden ub RB y z) :
    Same hidden ub (fun a c => ∃ b, RA a b ∧ RB b c) x z :=
  ⟨fun x z => ∃ y, Same hidden ub RA x y ∧ Same hidden ub RB y z,
   fun _ _ ⟨_, h₁, h₂⟩ => trans_step hbr (Same.unfold h₁) h₂, ⟨_, h₁, h₂⟩⟩

end Trans

/-! ## Bind -/

theorem next_bind {m n : CoFree E A} {f : A → CoFree E B} (h : Next hidden m n) :
    Next hidden (m.bind f) (n.bind f) := by
  rcases h with h | ⟨op, hop, k, hk, r, rfl⟩ | ⟨c, k, hk, r, rfl⟩
  · left; rw [observe_bind, h]; rfl
  · right; left; exact ⟨op, hop, _, by rw [observe_bind, hk]; rfl, r, rfl⟩
  · right; right; exact ⟨c, _, by rw [observe_bind, hk]; rfl, r, rfl⟩

theorem silent_bind {m : CoFree E A} {f : A → CoFree E B} :
    Silent hidden m → Silent hidden (m.bind f)
  | .inl ⟨_, hn⟩ => .inl ⟨_, next_bind hn⟩
  | .inr ⟨c, _, hk⟩ => .inr ⟨c, _, by rw [observe_bind, hk]; rfl⟩

theorem next_bind_inv {m : CoFree E A} {n' : CoFree E B} {f : A → CoFree E B}
    (hs : Silent hidden m) (h : Next hidden (m.bind f) n') :
    ∃ n, Next hidden m n ∧ n' = n.bind f := by
  cases hm : m.observe with
  | pure a => exact (not_silent_pure hm hs).elim
  | silent n =>
    rcases h with h | ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩ <;> rw [observe_bind, hm] at h <;> cases h
    exact ⟨n, .inl hm, rfl⟩
  | impure op k =>
    rcases h with h | ⟨_, hop, _, h, r, rfl⟩ | ⟨_, _, h, _⟩ <;> rw [observe_bind, hm] at h <;>
      cases h
    exact ⟨k r, .inr (.inl ⟨op, hop, k, hm, r, rfl⟩), rfl⟩
  | br c k =>
    rcases h with h | ⟨_, _, _, h, _⟩ | ⟨_, _, h, r, rfl⟩ <;> rw [observe_bind, hm] at h <;>
      cases h
    exact ⟨k r, .inr (.inr ⟨c, k, hm, r, rfl⟩), rfl⟩

theorem Same.bind {RR : A → B → Prop} {RR' : C → D → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    {f : A → CoFree E C} {g : B → CoFree E D} (h : Same hidden ub RR m₁ m₂)
    (hfg : ∀ a b, RR a b → Same hidden ub RR' (f a) (g b)) :
    Same hidden ub RR' (m₁.bind f) (m₂.bind g) := by
  refine Same.coind (fun x y => ∃ m₁ m₂, Same hidden ub RR m₁ m₂ ∧ x = m₁.bind f ∧
    y = m₂.bind g) ?_ ⟨m₁, m₂, h, rfl, rfl⟩
  rintro _ _ ⟨m₁, m₂, h, rfl, rfl⟩
  replace h := Same.unfold h
  induction h with
  | silent hs₁ hs₂ h =>
    refine .silent (silent_bind hs₁) (silent_bind hs₂) fun n₁ n₂ hn₁ hn₂ => ?_
    obtain ⟨n₁, h₁, rfl⟩ := next_bind_inv hs₁ hn₁
    obtain ⟨n₂, h₂, rfl⟩ := next_bind_inv hs₂ hn₂
    exact .inl ⟨_, _, h n₁ n₂ h₁ h₂, rfl, rfl⟩
  | impure op h₁ h₂ hop hk =>
    exact .impure op (by rw [observe_bind, h₁]; rfl) (by rw [observe_bind, h₂]; rfl) hop
      fun r => .inl ⟨_, _, hk r, rfl, rfl⟩
  | ret h₁ h₂ hab =>
    exact SameF.congr (SameF.mono (fun _ _ => .inr) (Same.unfold (hfg _ _ hab)))
      (by rw [observe_bind, h₁]; rfl) (by rw [observe_bind, h₂]; rfl)
  | ub op₁ op₂ h₁ h₂ hub₁ hub₂ hop₁ hop₂ =>
    exact .ub op₁ op₂ (by rw [observe_bind, h₁]; rfl) (by rw [observe_bind, h₂]; rfl)
      hub₁ hub₂ hop₁ hop₂
  | silentL hs _ ih =>
    refine .silentL (silent_bind hs) fun n' hn' => ?_
    obtain ⟨n, hn, rfl⟩ := next_bind_inv hs hn'
    exact ih n hn
  | silentR hs _ ih =>
    refine .silentR (silent_bind hs) fun n' hn' => ?_
    obtain ⟨n, hn, rfl⟩ := next_bind_inv hs hn'
    exact ih n hn

/-! ## Weak bisimulation -/

theorem Eutt.refl {RR : A → A → Prop} (hbr : E.BrOp → False) (hRR : ∀ a, RR a a)
    (m : CoFree E A) : Eutt RR m m :=
  Same.refl (fun _ h => h) hbr hRR m

theorem Eutt.of_bisim (hbr : E.BrOp → False) {m₁ m₂ : CoFree E A} (h : Bisim m₁ m₂) :
    Eutt Eq m₁ m₂ := by
  refine ⟨Bisim, fun x y ⟨R, hR, hxy⟩ => ?_, h⟩
  have hs := hR x y hxy
  generalize hx : x.observe = sx at hs
  generalize hy : y.observe = sy at hs
  cases hs with
  | pure a => exact .ret hx hy rfl
  | @silent n₁ n₂ h =>
    refine .silent (silent_of_silent hx) (silent_of_silent hy) fun n₁' n₂' h₁ h₂ => ?_
    rw [(next_silent_iff hx).mp h₁, (next_silent_iff hy).mp h₂]
    exact ⟨R, hR, h⟩
  | impure op h => exact .impure op hx hy id fun r => ⟨R, hR, h r⟩
  | br c _ => exact (hbr c).elim

end CoFree.Proofs
