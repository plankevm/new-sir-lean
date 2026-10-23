import ITree.Same.Proofs

universe u

namespace CoFree

variable {E : Effect.{u}} {A B C D : Type u} {ub : E.Op → Prop}

theorem next_congr {m m' n : CoFree E A} (he : m.observe = m'.observe) :
    Next m n → Next m' n :=
  Proofs.next_congr he

theorem silent_congr {m m' : CoFree E A} (he : m.observe = m'.observe) :
    Silent m → Silent m' :=
  Proofs.silent_congr he

theorem silent_of_next {m n : CoFree E A} : Next m n → Silent m :=
  Proofs.silent_of_next

theorem Silent.next {m : CoFree E A} : Silent m → ∃ n, Next m n :=
  Proofs.Silent.next

theorem not_silent_pure {m : CoFree E A} {a : A} (h : m.observe = .pure a) :
    ¬Silent m :=
  Proofs.not_silent_pure h

theorem not_silent_impure {m : CoFree E A} {op : E.Op} {k : E.Resp op → CoFree E A}
    (h : m.observe = .impure op k) : ¬Silent m :=
  Proofs.not_silent_impure h

theorem next_silent_iff {m n n' : CoFree E A} (h : m.observe = .silent n) :
    Next m n' ↔ n' = n :=
  Proofs.next_silent_iff h

theorem next_branch_iff {m n : CoFree E A} {c : E.BrOp} {k : E.BrResp c → CoFree E A}
    (h : m.observe = .branch c k) : Next m n ↔ ∃ r, k r = n :=
  Proofs.next_branch_iff h

theorem silent_of_silent {m n : CoFree E A} (h : m.observe = .silent n) : Silent m :=
  Proofs.silent_of_silent h

theorem silent_of_branch {m : CoFree E A} {c : E.BrOp} {k : E.BrResp c → CoFree E A}
    (h : m.observe = .branch c k) : Silent m :=
  Proofs.silent_of_branch h

theorem SameF.mono {RR : A → B → Prop} {R R' : CoFree E A → CoFree E B → Prop}
    (hR : ∀ x y, R x y → R' x y) {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : SameF ub RR R m₁ m₂) : SameF ub RR R' m₁ m₂ :=
  Proofs.SameF.mono hR h

theorem SameF.congr {RR : A → B → Prop} {R : CoFree E A → CoFree E B → Prop}
    {m₁ m₁' : CoFree E A} {m₂ m₂' : CoFree E B} (h : SameF ub RR R m₁ m₂)
    (he₁ : m₁.observe = m₁'.observe) (he₂ : m₂.observe = m₂'.observe) :
    SameF ub RR R m₁' m₂' :=
  Proofs.SameF.congr h he₁ he₂

theorem Same.unfold {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B} :
    Same ub RR m₁ m₂ → SameF ub RR (Same ub RR) m₁ m₂ :=
  Proofs.Same.unfold

theorem Same.fold {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : SameF ub RR (Same ub RR) m₁ m₂) : Same ub RR m₁ m₂ :=
  Proofs.Same.fold h

/-- Coinduction up to `Same`: `R` may step to pairs already known to be related. -/
theorem Same.coind {RR : A → B → Prop} (R : CoFree E A → CoFree E B → Prop)
    (hR : ∀ x y, R x y → SameF ub RR (fun x y => R x y ∨ Same ub RR x y) x y)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : R m₁ m₂) : Same ub RR m₁ m₂ :=
  Proofs.Same.coind R hR h

/-- Coinduction up to finitely many layers of `SameF` and up to `Same`. -/
theorem Same.coind_steps {RR : A → B → Prop} (R : CoFree E A → CoFree E B → Prop)
    (hR : ∀ x y, R x y → SameF ub RR (SameSteps ub RR R) x y)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : R m₁ m₂) : Same ub RR m₁ m₂ :=
  Proofs.Same.coind_steps R hR h

theorem Same.congr {RR : A → B → Prop} {m₁ m₁' : CoFree E A} {m₂ m₂' : CoFree E B}
    (h : Same ub RR m₁ m₂) (he₁ : m₁.observe = m₁'.observe)
    (he₂ : m₂.observe = m₂'.observe) : Same ub RR m₁' m₂' :=
  Proofs.Same.congr h he₁ he₂

theorem Same.silent {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs₁ : Silent m₁) (hs₂ : Silent m₂)
    (h : ∀ n₁ n₂, Next m₁ n₁ → Next m₂ n₂ → Same ub RR n₁ n₂) :
    Same ub RR m₁ m₂ :=
  Proofs.Same.silent hs₁ hs₂ h

theorem Same.impure {RR : A → B → Prop} (op : E.Op)
    {k₁ : E.Resp op → CoFree E A} {k₂ : E.Resp op → CoFree E B}
    (h : ∀ r, Same ub RR (k₁ r) (k₂ r)) :
    Same ub RR (CoFree.impure op k₁) (CoFree.impure op k₂) :=
  Proofs.Same.impure op h

theorem Same.ret {RR : A → B → Prop} {a : A} {b : B} (h : RR a b) :
    Same ub RR (CoFree.pure a : CoFree E A) (CoFree.pure b) :=
  Proofs.Same.ret h

theorem Same.undefined {RR : A → B → Prop} (op₁ op₂ : E.Op) (hub₁ : ub op₁) (hub₂ : ub op₂)
    (k₁ : E.Resp op₁ → CoFree E A) (k₂ : E.Resp op₂ → CoFree E B) :
    Same ub RR (CoFree.impure op₁ k₁) (CoFree.impure op₂ k₂) :=
  Proofs.Same.undefined op₁ op₂ hub₁ hub₂ k₁ k₂

theorem Same.silentL {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs : Silent m₁) (h : ∀ n, Next m₁ n → Same ub RR n m₂) :
    Same ub RR m₁ m₂ :=
  Proofs.Same.silentL hs h

theorem Same.silentR {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs : Silent m₂) (h : ∀ n, Next m₂ n → Same ub RR m₁ n) :
    Same ub RR m₁ m₂ :=
  Proofs.Same.silentR hs h

/-- A branch on the left: every response must be related. -/
theorem Same.branchL {RR : A → B → Prop} (c : E.BrOp) {k : E.BrResp c → CoFree E A}
    {m₂ : CoFree E B} (h : ∀ r, Same ub RR (k r) m₂) :
    Same ub RR (CoFree.branch c k) m₂ :=
  Proofs.Same.branchL c h

theorem Same.branchR {RR : A → B → Prop} {m₁ : CoFree E A} (c : E.BrOp)
    {k : E.BrResp c → CoFree E B} (h : ∀ r, Same ub RR m₁ (k r)) :
    Same ub RR m₁ (CoFree.branch c k) :=
  Proofs.Same.branchR c h

theorem Same.silentL_inv {RR : A → B → Prop} {m₁ n₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same ub RR m₁ m₂) (hn : Next m₁ n₁) : Same ub RR n₁ m₂ :=
  Proofs.Same.silentL_inv h hn

theorem Same.silentR_inv {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ n₂ : CoFree E B}
    (h : Same ub RR m₁ m₂) (hn : Next m₂ n₂) : Same ub RR m₁ n₂ :=
  Proofs.Same.silentR_inv h hn

/-- Two visible, defined operations that are related are the same operation. -/
theorem Same.impure_inv {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    {op₁ op₂ : E.Op} {k₁ : E.Resp op₁ → CoFree E A} {k₂ : E.Resp op₂ → CoFree E B}
    (h : Same ub RR m₁ m₂) (h₁ : m₁.observe = .impure op₁ k₁)
    (h₂ : m₂.observe = .impure op₂ k₂) (hub₁ : ¬ub op₁) : op₁ = op₂ :=
  Proofs.Same.impure_inv h h₁ h₂ hub₁

theorem Same.symm {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same ub RR m₁ m₂) : Same ub (fun b a => RR a b) m₂ m₁ :=
  Proofs.Same.symm h

theorem Same.mono {RR RR' : A → B → Prop} (hRR : ∀ a b, RR a b → RR' a b)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : Same ub RR m₁ m₂) :
    Same ub RR' m₁ m₂ :=
  Proofs.Same.mono hRR h

theorem Same.refl {RR : A → A → Prop}
    (hbr : E.BrOp → False) (hRR : ∀ a, RR a a) (m : CoFree E A) : Same ub RR m m :=
  Proofs.Same.refl hbr hRR m

theorem Same.trans {RA : A → B → Prop} {RB : B → C → Prop} {x : CoFree E A} {y : CoFree E B}
    {z : CoFree E C} (h₁ : Same ub RA x y) (h₂ : Same ub RB y z) :
    Same ub (fun a c => ∃ b, RA a b ∧ RB b c) x z :=
  Proofs.Same.trans h₁ h₂

theorem next_bind {m n : CoFree E A} {f : A → CoFree E B} (h : Next m n) :
    Next (m.bind f) (n.bind f) :=
  Proofs.next_bind h

theorem silent_bind {m : CoFree E A} {f : A → CoFree E B} :
    Silent m → Silent (m.bind f) :=
  Proofs.silent_bind

theorem next_bind_inv {m : CoFree E A} {n' : CoFree E B} {f : A → CoFree E B}
    (hs : Silent m) (h : Next (m.bind f) n') :
    ∃ n, Next m n ∧ n' = n.bind f :=
  Proofs.next_bind_inv hs h

theorem Same.bind {RR : A → B → Prop} {RR' : C → D → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    {f : A → CoFree E C} {g : B → CoFree E D} (h : Same ub RR m₁ m₂)
    (hfg : ∀ a b, RR a b → Same ub RR' (f a) (g b)) :
    Same ub RR' (m₁.bind f) (m₂.bind g) :=
  Proofs.Same.bind h hfg

theorem Eutt.refl {RR : A → A → Prop} (hbr : E.BrOp → False) (hRR : ∀ a, RR a a)
    (m : CoFree E A) : Eutt RR m m :=
  Proofs.Eutt.refl hbr hRR m

theorem Eutt.of_bisim (hbr : E.BrOp → False) {m₁ m₂ : CoFree E A} (h : Bisim m₁ m₂) :
    Eutt Eq m₁ m₂ :=
  Proofs.Eutt.of_bisim hbr h

end CoFree
