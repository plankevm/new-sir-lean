import ITree.Same.Proofs

universe u

namespace CoFree

variable {E : Effect.{u}} {N N₁ N₂ N₃ : NonDeterminism.{u}} {A B C D : Type u} {Ret : A → B → Prop}
  {RA : A → B → Prop} {RB : B → C → Prop}

/-! ## Unobserved steps -/

theorem forallUnobserved_mono {m : CoFree E N₁ A} {p q : CoFree E N₁ A → Prop}
    (h : ForallUnobserved m p) (hpq : ∀ n, p n → q n) : ForallUnobserved m q :=
  Proofs.forallUnobserved_mono h hpq

theorem forallUnobserved_congr {m m' : CoFree E N₁ A} {p : CoFree E N₁ A → Prop}
    (he : m.observe = m'.observe) (h : ForallUnobserved m p) : ForallUnobserved m' p :=
  Proofs.forallUnobserved_congr he h

theorem forallUnobserved_silent {m n : CoFree E N₁ A} {p : CoFree E N₁ A → Prop}
    (h : m.observe = .silent n) : ForallUnobserved m p ↔ p n :=
  Proofs.forallUnobserved_silent h

theorem forallUnobserved_branch {m : CoFree E N₁ A} {c : N₁.Op} {k : N₁.Resp c → CoFree E N₁ A}
    {p : CoFree E N₁ A → Prop} (h : m.observe = .branch c k) :
    ForallUnobserved m p ↔ ∀ r, p (k r) :=
  Proofs.forallUnobserved_branch h

theorem not_forallUnobserved_pure {m : CoFree E N₁ A} {a : A} {p : CoFree E N₁ A → Prop}
    (h : m.observe = .pure a) : ¬ForallUnobserved m p :=
  Proofs.not_forallUnobserved_pure h

theorem not_forallUnobserved_impure {m : CoFree E N₁ A} {op : E.Op} {k : E.Resp op → CoFree E N₁ A}
    {p : CoFree E N₁ A → Prop} (h : m.observe = .impure op k) : ¬ForallUnobserved m p :=
  Proofs.not_forallUnobserved_impure h

/-- An unobserved step has a successor, since every branch has a response. -/
theorem forallUnobserved_exists {m : CoFree E N₁ A} {p q : CoFree E N₁ A → Prop}
    (hp : ForallUnobserved m p) (hq : ForallUnobserved m q) : ∃ n, p n ∧ q n :=
  Proofs.forallUnobserved_exists hp hq

/-! ## One layer -/

/-- Finitely many unobserved steps on the left, as one rule. -/
theorem sameFinite_unobservedL {R : CoFree E N₁ A → CoFree E N₂ B → Prop} {m₁ : CoFree E N₁ A}
    {m₂ : CoFree E N₂ B} (h : ForallUnobserved m₁ fun n => SameFinite Ret R n m₂) :
    SameFinite Ret R m₁ m₂ :=
  Proofs.sameFinite_unobservedL h

theorem sameFinite_unobservedR {R : CoFree E N₁ A → CoFree E N₂ B → Prop} {m₁ : CoFree E N₁ A}
    {m₂ : CoFree E N₂ B} (h : ForallUnobserved m₂ fun n => SameFinite Ret R m₁ n) :
    SameFinite Ret R m₁ m₂ :=
  Proofs.sameFinite_unobservedR h

theorem SameFinite.mono {R R' : CoFree E N₁ A → CoFree E N₂ B → Prop}
    (hR : ∀ x y, R x y → R' x y) {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h : SameFinite Ret R m₁ m₂) : SameFinite Ret R' m₁ m₂ :=
  Proofs.SameFinite.mono hR h

theorem SameFinite.congr {R : CoFree E N₁ A → CoFree E N₂ B → Prop}
    {m₁ m₁' : CoFree E N₁ A} {m₂ m₂' : CoFree E N₂ B} (h : SameFinite Ret R m₁ m₂)
    (he₁ : m₁.observe = m₁'.observe) (he₂ : m₂.observe = m₂'.observe) :
    SameFinite Ret R m₁' m₂' :=
  Proofs.SameFinite.congr h he₁ he₂

/-! ## The fixed point -/

theorem Same.unfold {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} :
    Same Ret m₁ m₂ → SameFinite Ret (Same Ret) m₁ m₂ :=
  Proofs.Same.unfold

theorem Same.fold {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h : SameFinite Ret (Same Ret) m₁ m₂) : Same Ret m₁ m₂ :=
  Proofs.Same.fold h

/-- Coinduction up to `Same`: `R` may step to pairs already known to be related. -/
theorem Same.coind (R : CoFree E N₁ A → CoFree E N₂ B → Prop)
    (hR : ∀ x y, R x y → SameFinite Ret (fun x y => R x y ∨ Same Ret x y) x y)
    {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} (h : R m₁ m₂) : Same Ret m₁ m₂ :=
  Proofs.Same.coind R hR h

theorem Same.congr {m₁ m₁' : CoFree E N₁ A} {m₂ m₂' : CoFree E N₂ B}
    (h : Same Ret m₁ m₂) (he₁ : m₁.observe = m₁'.observe)
    (he₂ : m₂.observe = m₂'.observe) : Same Ret m₁' m₂' :=
  Proofs.Same.congr h he₁ he₂

/-! ## Constructors -/

theorem Same.ret {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} {a : A} {b : B}
    (h₁ : m₁.observe = .pure a) (h₂ : m₂.observe = .pure b) (h : Ret a b) :
    Same Ret m₁ m₂ :=
  Proofs.Same.ret h₁ h₂ h

theorem Same.impure {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} (op : E.Op)
    {k₁ : E.Resp op → CoFree E N₁ A} {k₂ : E.Resp op → CoFree E N₂ B}
    (h₁ : m₁.observe = .impure op k₁) (h₂ : m₂.observe = .impure op k₂)
    (h : ∀ r, Same Ret (k₁ r) (k₂ r)) : Same Ret m₁ m₂ :=
  Proofs.Same.impure op h₁ h₂ h

theorem Same.silentL {m₁ n₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h₁ : m₁.observe = .silent n₁) (h : Same Ret n₁ m₂) : Same Ret m₁ m₂ :=
  Proofs.Same.silentL h₁ h

theorem Same.silentR {m₁ : CoFree E N₁ A} {m₂ n₂ : CoFree E N₂ B}
    (h₂ : m₂.observe = .silent n₂) (h : Same Ret m₁ n₂) : Same Ret m₁ m₂ :=
  Proofs.Same.silentR h₂ h

theorem Same.branchL {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} (c : N₁.Op)
    {k : N₁.Resp c → CoFree E N₁ A} (h₁ : m₁.observe = .branch c k)
    (h : ∀ r, Same Ret (k r) m₂) : Same Ret m₁ m₂ :=
  Proofs.Same.branchL c h₁ h

theorem Same.branchR {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} (c : N₂.Op)
    {k : N₂.Resp c → CoFree E N₂ B} (h₂ : m₂.observe = .branch c k)
    (h : ∀ r, Same Ret m₁ (k r)) : Same Ret m₁ m₂ :=
  Proofs.Same.branchR c h₂ h

theorem Same.mutualUnobservedStep {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h : ForallUnobserved m₁ fun n₁ => ForallUnobserved m₂ (Same Ret n₁)) : Same Ret m₁ m₂ :=
  Proofs.Same.mutualUnobservedStep h

/-- Both sides branch: every pair of responses must be related. -/
theorem Same.branch {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} {c₁ : N₁.Op} {c₂ : N₂.Op}
    {k₁ : N₁.Resp c₁ → CoFree E N₁ A} {k₂ : N₂.Resp c₂ → CoFree E N₂ B}
    (h₁ : m₁.observe = .branch c₁ k₁) (h₂ : m₂.observe = .branch c₂ k₂)
    (h : ∀ r₁ r₂, Same Ret (k₁ r₁) (k₂ r₂)) : Same Ret m₁ m₂ :=
  Proofs.Same.branch h₁ h₂ h

/-! ## Inversion -/

theorem Same.silentL_inv {m₁ n₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .silent n₁) : Same Ret n₁ m₂ :=
  Proofs.Same.silentL_inv h h₁

theorem Same.silentR_inv {m₁ : CoFree E N₁ A} {m₂ n₂ : CoFree E N₂ B}
    (h : Same Ret m₁ m₂) (h₂ : m₂.observe = .silent n₂) : Same Ret m₁ n₂ :=
  Proofs.Same.silentR_inv h h₂

theorem Same.branchL_inv {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} {c : N₁.Op}
    {k : N₁.Resp c → CoFree E N₁ A} (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .branch c k)
    (r : N₁.Resp c) : Same Ret (k r) m₂ :=
  Proofs.Same.branchL_inv h h₁ r

theorem Same.branchR_inv {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} {c : N₂.Op}
    {k : N₂.Resp c → CoFree E N₂ B} (h : Same Ret m₁ m₂) (h₂ : m₂.observe = .branch c k)
    (r : N₂.Resp c) : Same Ret m₁ (k r) :=
  Proofs.Same.branchR_inv h h₂ r

/-- After an unobserved step on the left, the successors are still related. -/
theorem Same.unobservedL_inv {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} (h : Same Ret m₁ m₂)
    (hu : ForallUnobserved m₁ fun _ => True) : ForallUnobserved m₁ fun n => Same Ret n m₂ :=
  Proofs.Same.unobservedL_inv h hu

theorem Same.unobservedR_inv {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} (h : Same Ret m₁ m₂)
    (hu : ForallUnobserved m₂ fun _ => True) : ForallUnobserved m₂ fun n => Same Ret m₁ n :=
  Proofs.Same.unobservedR_inv h hu

theorem Same.ret_inv {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} {a : A} {b : B}
    (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .pure a) (h₂ : m₂.observe = .pure b) : Ret a b :=
  Proofs.Same.ret_inv h h₁ h₂

/-- Two related visible operations are the same operation. -/
theorem Same.impure_inv {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    {op₁ op₂ : E.Op} {k₁ : E.Resp op₁ → CoFree E N₁ A} {k₂ : E.Resp op₂ → CoFree E N₂ B}
    (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .impure op₁ k₁)
    (h₂ : m₂.observe = .impure op₂ k₂) : op₁ = op₂ :=
  Proofs.Same.impure_inv h h₁ h₂

/-- Related machines performing the same operation stay related for every response. -/
theorem Same.impure_inv_resp {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    {op : E.Op} {k₁ : E.Resp op → CoFree E N₁ A} {k₂ : E.Resp op → CoFree E N₂ B}
    (h : Same Ret m₁ m₂) (h₁ : m₁.observe = .impure op k₁)
    (h₂ : m₂.observe = .impure op k₂) (r : E.Resp op) : Same Ret (k₁ r) (k₂ r) :=
  Proofs.Same.impure_inv_resp h h₁ h₂ r

/-! ## Equivalence-like laws and bind -/

theorem Same.symm {Ret : A → B → Prop} {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h : Same Ret m₁ m₂) : Same (fun b a => Ret a b) m₂ m₁ :=
  Proofs.Same.symm h

theorem Same.mono {Ret Ret' : A → B → Prop} (hRet : ∀ a b, Ret a b → Ret' a b)
    {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} (h : Same Ret m₁ m₂) :
    Same Ret' m₁ m₂ :=
  Proofs.Same.mono hRet h

theorem Same.refl {Ret : A → A → Prop}
    (hbr : N₁.Op → False) (hRet : ∀ a, Ret a a) (m : CoFree E N₁ A) : Same Ret m m :=
  Proofs.Same.refl hbr hRet m

theorem Same.trans {x : CoFree E N₁ A} {y : CoFree E N₂ B} {z : CoFree E N₃ C}
    (h₁ : Same RA x y) (h₂ : Same RB y z) :
    Same (fun a c => ∃ b, RA a b ∧ RB b c) x z :=
  Proofs.Same.trans h₁ h₂

theorem Same.symm_eq {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ A} (h : Same Eq m₁ m₂) : Same Eq m₂ m₁ :=
  Proofs.Same.symm_eq h

theorem Same.trans_eq {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ A} {m₃ : CoFree E N₃ A} (h₁ : Same Eq m₁ m₂) (h₂ : Same Eq m₂ m₃) :
    Same Eq m₁ m₃ :=
  Proofs.Same.trans_eq h₁ h₂

/-! ## Determinism

A machine related to anything is related to itself, but only up to `Ret ∘ Ret⁻¹`: two results
of `m₁` count as equal when some result of `m₂` is related to both. With a coarse `Ret` (e.g.
`fun _ _ => True`) this says nothing about results, so a machine whose result depends on a branch
response is still "deterministic"; only its visible operations are pinned down. With `Ret := Eq`
it is determinism of results too. -/

theorem Same.deterministic_left {Ret : A → B → Prop} {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h : Same Ret m₁ m₂) : Same (fun a a' => ∃ b, Ret a b ∧ Ret a' b) m₁ m₁ :=
  Proofs.Same.deterministic_left h

theorem Same.deterministic_right {Ret : A → B → Prop} {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h : Same Ret m₁ m₂) : Same (fun b b' => ∃ a, Ret a b ∧ Ret a b') m₂ m₂ :=
  Proofs.Same.deterministic_right h

/-- Only deterministic machines are related to anything. -/
theorem Deterministic.of_same {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ A} (h : Same Eq m₁ m₂) :
    Deterministic m₁ ∧ Deterministic m₂ :=
  Proofs.Deterministic.of_same h

/-- A machine related to itself under no relation is related to nothing. -/
theorem Same.not_of_not_self_left {Ret : A → B → Prop} {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (hself : ∀ R : A → A → Prop, ¬Same R m₁ m₁) : ¬Same Ret m₁ m₂ :=
  Proofs.Same.not_of_not_self_left hself

theorem Same.not_of_not_self_right {Ret : A → B → Prop} {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (hself : ∀ R : B → B → Prop, ¬Same R m₂ m₂) : ¬Same Ret m₁ m₂ :=
  Proofs.Same.not_of_not_self_right hself

theorem Same.bind {Ret : A → B → Prop} {Ret' : C → D → Prop} {m₁ : CoFree E N₁ A}
    {m₂ : CoFree E N₂ B} {f : A → CoFree E N₁ C} {g : B → CoFree E N₂ D} (h : Same Ret m₁ m₂)
    (hfg : ∀ a b, Ret a b → Same Ret' (f a) (g b)) :
    Same Ret' (m₁.bind f) (m₂.bind g) :=
  Proofs.Same.bind h hfg

/-! ## Sanity checks of the definition -/

@[simp]
theorem spin_observe : (spin : CoFree E N₁ A).observe = .silent spin :=
  Proofs.spin_observe

theorem spin_relates_to_self : ∀ {E N₁ N₂ A B Ret}, Same Ret (spin (E := E) (N := N₁) (A := A)) (spin (E := E) (N := N₂) (A := B)) :=
  Proofs.spin_relates_to_self

/-- A machine that only runs silently is related to no machine that returns. -/
theorem Same.not_spin_pure {b : B} : ¬Same Ret (spin : CoFree E N₁ A) (CoFree.pure b : CoFree E N₂ B) :=
  Proofs.Same.not_spin_pure

/-- Nor to one that performs an operation. -/
theorem Same.not_spin_impure {op : E.Op} {k : E.Resp op → CoFree E N₂ B} :
    ¬Same Ret (spin : CoFree E N₁ A) (CoFree.impure op k) :=
  Proofs.Same.not_spin_impure

theorem Same.pure_iff {a : A} {b : B} :
    Same Ret (CoFree.pure a : CoFree E N₁ A) (CoFree.pure b : CoFree E N₂ B) ↔ Ret a b :=
  Proofs.Same.pure_iff

/-- A silent step on the left is invisible. -/
theorem Same.silent_iff_left {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} :
    Same Ret (CoFree.silent m₁) m₂ ↔ Same Ret m₁ m₂ :=
  Proofs.Same.silent_iff_left

theorem Same.silent_iff_right {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} :
    Same Ret m₁ (CoFree.silent m₂) ↔ Same Ret m₁ m₂ :=
  Proofs.Same.silent_iff_right

theorem Same.impure_iff {op : E.Op} {k₁ : E.Resp op → CoFree E N₁ A}
    {k₂ : E.Resp op → CoFree E N₂ B} :
    Same Ret (CoFree.impure op k₁) (CoFree.impure op k₂) ↔ ∀ r, Same Ret (k₁ r) (k₂ r) :=
  Proofs.Same.impure_iff

theorem Same.impure_ne {op₁ op₂ : E.Op} {k₁ : E.Resp op₁ → CoFree E N₁ A}
    {k₂ : E.Resp op₂ → CoFree E N₂ B} (hne : op₁ ≠ op₂) :
    ¬Same Ret (CoFree.impure op₁ k₁) (CoFree.impure op₂ k₂) :=
  Proofs.Same.impure_ne hne

/-- An operation with no response ends the run (undefined behavior is one): it relates to itself,
whatever the continuations. -/
theorem Same.terminal {op : E.Op} (hop : E.Resp op → False) (k₁ : E.Resp op → CoFree E N₁ A)
    (k₂ : E.Resp op → CoFree E N₂ B) : Same Ret (CoFree.impure op k₁) (CoFree.impure op k₂) :=
  Proofs.Same.terminal hop k₁ k₂

/-- Two branches are related iff every pair of responses is. -/
theorem Same.branch_iff {c₁ : N₁.Op} {c₂ : N₂.Op} {k₁ : N₁.Resp c₁ → CoFree E N₁ A}
    {k₂ : N₂.Resp c₂ → CoFree E N₂ B} :
    Same Ret (CoFree.branch c₁ k₁) (CoFree.branch c₂ k₂) ↔
      ∀ r₁ r₂, Same Ret (k₁ r₁) (k₂ r₂) :=
  Proofs.Same.branch_iff

/-- A branch on the left is related iff every response is. -/
theorem Same.branch_iff_left {c : N₁.Op} {k : N₁.Resp c → CoFree E N₁ A} {m₂ : CoFree E N₂ B} :
    Same Ret (CoFree.branch c k) m₂ ↔ ∀ r, Same Ret (k r) m₂ :=
  Proofs.Same.branch_iff_left

/-- A branch that ignores its response is invisible. -/
theorem Same.branch_const {c : N₁.Op} {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B} :
    Same Ret (CoFree.branch c fun _ => m₁) m₂ ↔ Same Ret m₁ m₂ :=
  Proofs.Same.branch_const

/-- A machine whose visible behavior depends on a branch is not related to itself. -/
theorem Same.not_refl_of_branch {Ret : A → A → Prop} {m : CoFree E N₁ A} {c : N₁.Op}
    {k : N₁.Resp c → CoFree E N₁ A} (h : m.observe = .branch c k) {r₁ r₂ : N₁.Resp c}
    (hne : ¬Same Ret (k r₁) (k r₂)) : ¬Same Ret m m :=
  Proofs.Same.not_refl_of_branch h hne

/-- Divergence absorbs branches: branching into machines that all diverge is the same as
diverging. -/
theorem Same.spin_branch_spin {c : N₂.Op} :
    Same Ret (spin : CoFree E N₁ A) (CoFree.branch c fun _ => (spin : CoFree E N₂ B)) :=
  Proofs.Same.spin_branch_spin

end CoFree
