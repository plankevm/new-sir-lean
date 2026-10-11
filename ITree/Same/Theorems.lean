import ITree.Same.Proofs

universe u

namespace CoFree

variable {E : Effect.{u}} {A B C D : Type u} {hidden ub : E.Op → Prop}

theorem next_congr {m m' n : CoFree E A} (he : m.observe = m'.observe) :
    Next hidden m n → Next hidden m' n :=
  Proofs.next_congr he

theorem silent_congr {m m' : CoFree E A} (he : m.observe = m'.observe) :
    Silent hidden m → Silent hidden m' :=
  Proofs.silent_congr he

theorem not_silent_pure {m : CoFree E A} {a : A} (h : m.observe = .pure a) :
    ¬Silent hidden m :=
  Proofs.not_silent_pure h

theorem not_silent_impure {m : CoFree E A} {op : E.Op} {k : E.Resp op → CoFree E A}
    (h : m.observe = .impure op k) (hop : ¬hidden op) : ¬Silent hidden m :=
  Proofs.not_silent_impure h hop

theorem next_silent_iff {m n n' : CoFree E A} (h : m.observe = .silent n) :
    Next hidden m n' ↔ n' = n :=
  Proofs.next_silent_iff h

theorem next_hidden_iff {m n : CoFree E A} {op : E.Op} {k : E.Resp op → CoFree E A}
    (h : m.observe = .impure op k) (hop : hidden op) : Next hidden m n ↔ ∃ r, k r = n :=
  Proofs.next_hidden_iff h hop

theorem silent_of_silent {m n : CoFree E A} (h : m.observe = .silent n) : Silent hidden m :=
  Proofs.silent_of_silent h

theorem silent_of_hidden {m : CoFree E A} {op : E.Op} {k : E.Resp op → CoFree E A}
    (h : m.observe = .impure op k) (hop : hidden op) (r : E.Resp op) : Silent hidden m :=
  Proofs.silent_of_hidden h hop r

theorem SameF.mono {RR : A → B → Prop} {R R' : CoFree E A → CoFree E B → Prop}
    (hR : ∀ x y, R x y → R' x y) {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : SameF hidden ub RR R m₁ m₂) : SameF hidden ub RR R' m₁ m₂ :=
  Proofs.SameF.mono hR h

theorem SameF.congr {RR : A → B → Prop} {R : CoFree E A → CoFree E B → Prop}
    {m₁ m₁' : CoFree E A} {m₂ m₂' : CoFree E B} (h : SameF hidden ub RR R m₁ m₂)
    (he₁ : m₁.observe = m₁'.observe) (he₂ : m₂.observe = m₂'.observe) :
    SameF hidden ub RR R m₁' m₂' :=
  Proofs.SameF.congr h he₁ he₂

theorem Same.unfold {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B} :
    Same hidden ub RR m₁ m₂ → SameF hidden ub RR (Same hidden ub RR) m₁ m₂ :=
  Proofs.Same.unfold

theorem Same.fold {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : SameF hidden ub RR (Same hidden ub RR) m₁ m₂) : Same hidden ub RR m₁ m₂ :=
  Proofs.Same.fold h

/-- Coinduction up to `Same`: `R` may step to pairs already known to be related. -/
theorem Same.coind {RR : A → B → Prop} (R : CoFree E A → CoFree E B → Prop)
    (hR : ∀ x y, R x y → SameF hidden ub RR (fun x y => R x y ∨ Same hidden ub RR x y) x y)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : R m₁ m₂) : Same hidden ub RR m₁ m₂ :=
  Proofs.Same.coind R hR h

/-- Coinduction up to finitely many layers of `SameF` and up to `Same`. -/
theorem Same.coind_steps {RR : A → B → Prop} (R : CoFree E A → CoFree E B → Prop)
    (hR : ∀ x y, R x y → SameF hidden ub RR (SameSteps hidden ub RR R) x y)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : R m₁ m₂) : Same hidden ub RR m₁ m₂ :=
  Proofs.Same.coind_steps R hR h

theorem Same.congr {RR : A → B → Prop} {m₁ m₁' : CoFree E A} {m₂ m₂' : CoFree E B}
    (h : Same hidden ub RR m₁ m₂) (he₁ : m₁.observe = m₁'.observe)
    (he₂ : m₂.observe = m₂'.observe) : Same hidden ub RR m₁' m₂' :=
  Proofs.Same.congr h he₁ he₂

theorem Same.silent {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs₁ : Silent hidden m₁) (hs₂ : Silent hidden m₂)
    (h : ∀ n₁ n₂, Next hidden m₁ n₁ → Next hidden m₂ n₂ → Same hidden ub RR n₁ n₂) :
    Same hidden ub RR m₁ m₂ :=
  Proofs.Same.silent hs₁ hs₂ h

theorem Same.impure {RR : A → B → Prop} (op : E.Op) (hop : ¬hidden op)
    {k₁ : E.Resp op → CoFree E A} {k₂ : E.Resp op → CoFree E B}
    (h : ∀ r, Same hidden ub RR (k₁ r) (k₂ r)) :
    Same hidden ub RR (CoFree.impure op k₁) (CoFree.impure op k₂) :=
  Proofs.Same.impure op hop h

theorem Same.ret {RR : A → B → Prop} {a : A} {b : B} (h : RR a b) :
    Same hidden ub RR (CoFree.pure a : CoFree E A) (CoFree.pure b) :=
  Proofs.Same.ret h

theorem Same.undefined {RR : A → B → Prop} (op₁ op₂ : E.Op) (hub₁ : ub op₁) (hub₂ : ub op₂)
    (hop₁ : ¬hidden op₁) (hop₂ : ¬hidden op₂)
    (k₁ : E.Resp op₁ → CoFree E A) (k₂ : E.Resp op₂ → CoFree E B) :
    Same hidden ub RR (CoFree.impure op₁ k₁) (CoFree.impure op₂ k₂) :=
  Proofs.Same.undefined op₁ op₂ hub₁ hub₂ hop₁ hop₂ k₁ k₂

theorem Same.silentL {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs : Silent hidden m₁) (h : ∀ n, Next hidden m₁ n → Same hidden ub RR n m₂) :
    Same hidden ub RR m₁ m₂ :=
  Proofs.Same.silentL hs h

theorem Same.silentR {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (hs : Silent hidden m₂) (h : ∀ n, Next hidden m₂ n → Same hidden ub RR m₁ n) :
    Same hidden ub RR m₁ m₂ :=
  Proofs.Same.silentR hs h

theorem Same.silentL_inv {RR : A → B → Prop} {m₁ n₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same hidden ub RR m₁ m₂) (hn : Next hidden m₁ n₁) : Same hidden ub RR n₁ m₂ :=
  Proofs.Same.silentL_inv h hn

theorem Same.silentR_inv {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ n₂ : CoFree E B}
    (h : Same hidden ub RR m₁ m₂) (hn : Next hidden m₂ n₂) : Same hidden ub RR m₁ n₂ :=
  Proofs.Same.silentR_inv h hn

/-- Two visible, defined operations that are related are the same operation. -/
theorem Same.impure_inv {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    {op₁ op₂ : E.Op} {k₁ : E.Resp op₁ → CoFree E A} {k₂ : E.Resp op₂ → CoFree E B}
    (h : Same hidden ub RR m₁ m₂) (h₁ : m₁.observe = .impure op₁ k₁)
    (h₂ : m₂.observe = .impure op₂ k₂) (hop₁ : ¬hidden op₁) (hop₂ : ¬hidden op₂)
    (hub₁ : ¬ub op₁) : op₁ = op₂ :=
  Proofs.Same.impure_inv h h₁ h₂ hop₁ hop₂ hub₁

theorem Same.symm {RR : A → B → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    (h : Same hidden ub RR m₁ m₂) : Same hidden ub (fun b a => RR a b) m₂ m₁ :=
  Proofs.Same.symm h

theorem Same.mono {RR RR' : A → B → Prop} (hRR : ∀ a b, RR a b → RR' a b)
    {m₁ : CoFree E A} {m₂ : CoFree E B} (h : Same hidden ub RR m₁ m₂) :
    Same hidden ub RR' m₁ m₂ :=
  Proofs.Same.mono hRR h

theorem Same.refl {RR : A → A → Prop} (hhidden : ∀ op, ¬hidden op) (hRR : ∀ a, RR a a)
    (m : CoFree E A) : Same hidden ub RR m m :=
  Proofs.Same.refl hhidden hRR m

theorem Same.trans {RA : A → B → Prop} {RB : B → C → Prop} {x : CoFree E A} {y : CoFree E B} {z : CoFree E C}
    (h₁ : Same hidden ub RA x y) (h₂ : Same hidden ub RB y z) :
    Same hidden ub (fun a c => ∃ b, RA a b ∧ RB b c) x z :=
  Proofs.Same.trans h₁ h₂

theorem next_bind {m n : CoFree E A} {f : A → CoFree E B} (h : Next hidden m n) :
    Next hidden (m.bind f) (n.bind f) :=
  Proofs.next_bind h

theorem silent_bind {m : CoFree E A} {f : A → CoFree E B} :
    Silent hidden m → Silent hidden (m.bind f) :=
  Proofs.silent_bind

theorem next_bind_inv {m : CoFree E A} {n' : CoFree E B} {f : A → CoFree E B}
    (hs : Silent hidden m) (h : Next hidden (m.bind f) n') :
    ∃ n, Next hidden m n ∧ n' = n.bind f :=
  Proofs.next_bind_inv hs h

theorem Same.bind {RR : A → B → Prop} {RR' : C → D → Prop} {m₁ : CoFree E A} {m₂ : CoFree E B}
    {f : A → CoFree E C} {g : B → CoFree E D} (h : Same hidden ub RR m₁ m₂)
    (hfg : ∀ a b, RR a b → Same hidden ub RR' (f a) (g b)) :
    Same hidden ub RR' (m₁.bind f) (m₂.bind g) :=
  Proofs.Same.bind h hfg

theorem Eutt.refl {RR : A → A → Prop} (hRR : ∀ a, RR a a) (m : CoFree E A) : Eutt RR m m :=
  Proofs.Eutt.refl hRR m

theorem Eutt.of_bisim {m₁ m₂ : CoFree E A} (h : Bisim m₁ m₂) : Eutt Eq m₁ m₂ :=
  Proofs.Eutt.of_bisim h

end CoFree
