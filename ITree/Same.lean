import ITree.Machine

/-! Weak bisimulation with branches.

`Same Ret m₁ m₂`: the two machines perform the same operations in the same order and return
values related by `Ret`, ignoring finitely many unobserved steps on either side at a time. An
unobserved step is a `silent` node or a `branch` node. A machine that runs unobserved forever is
related only to another such machine.

A branch is a choice of the machine's nondeterminism (`CoFree E N A`, choices `N`). It is
taken with each of its responses, on each side independently, and the two sides must agree for
every pair of responses: it models a choice the environment makes that the program may not
depend on (in SIR, where an allocation is placed). The two sides may have different
nondeterminism: only their operations are observed. So `Same` is a partial equivalence, not an
equivalence: a program whose visible behavior depends on a branch's response is not related to
itself. `Deterministic m` says that it is.

Every branch has a response (`NonDeterminism.resp_nonempty`); a branch with none would be
vacuously related to every machine.

An operation with no response (`E.Resp op` empty) ends the run; two such operations are related
exactly when they are the same operation, arguments included.

With no branches, `Same` is the usual weak bisimulation ("equivalence up to taus"), and is
reflexive. -/

universe u

namespace CoFree

variable {E : Effect.{u}} {N N₁ N₂ : NonDeterminism.{u}} {A B : Type u}

/-- `m` takes an unobserved step, and `p` holds after it, whichever response a branch takes. -/
def ForallUnobserved (m : CoFree E N A) (p : CoFree E N A → Prop) : Prop :=
  match m.observe with
  | .silent m' => p m'
  | .branch _op c => ∀ res, p (c res)
  | _ => False

/-- One layer of `Same`, with `CoindRec` for the pairs still to be checked. `ret`, `impure` and
`mutualUnobservedStep` make progress; the other four stay in `SameFinite`, so they can skip only
finitely many unobserved steps on one side in a row. -/
inductive SameFinite
  (Ret : A → B → Prop)
  (CoindRec : CoFree E N₁ A → CoFree E N₂ B → Prop)
    : CoFree E N₁ A → CoFree E N₂ B → Prop
  | ret {m₁ m₂} (a : A) (b : B) :
      m₁.observe = .pure a →
      m₂.observe = .pure b →
      Ret a b →
        SameFinite Ret CoindRec m₁ m₂
  | impure {m₁ m₂} (op : E.Op) {c₁ c₂} :
      m₁.observe = .impure op c₁ →
      m₂.observe = .impure op c₂ →
      (∀ res, CoindRec (c₁ res) (c₂ res)) →
        SameFinite Ret CoindRec m₁ m₂
  -- silentL/R branchL/R do not use `ForallUnobserved` because the kernel's positivity check doesn't
  -- unfold definitions
  | silentL {m₁ m₁' m₂} :
      m₁.observe = .silent m₁' →
      SameFinite Ret CoindRec m₁' m₂ →
        SameFinite Ret CoindRec m₁ m₂
  | silentR {m₁ m₂ m₂'} :
      m₂.observe = .silent m₂' →
      SameFinite Ret CoindRec m₁ m₂' →
        SameFinite Ret CoindRec m₁ m₂
  | branchL {m₁ m₂} (op : N₁.Op) {cₗ} :
      m₁.observe = .branch op cₗ →
      (∀ res, SameFinite Ret CoindRec (cₗ res) m₂) →
        SameFinite Ret CoindRec m₁ m₂
  | branchR {m₁ m₂} (op : N₂.Op) {cᵣ} :
      m₂.observe = .branch op cᵣ →
      (∀ res, SameFinite Ret CoindRec m₁ (cᵣ res)) →
        SameFinite Ret CoindRec m₁ m₂
  | mutualUnobservedStep {m₁ m₂} :
      ForallUnobserved m₁ (fun m₁' => ForallUnobserved m₂ (CoindRec m₁')) →
        SameFinite Ret CoindRec m₁ m₂

/-- The greatest fixed point of `SameFinite`: some relation containing the pair is closed under
`SameFinite`. -/
def Same (Ret : A → B → Prop) (m₁ : CoFree E N₁ A) (m₂ : CoFree E N₂ B) : Prop :=
  ∃ CoindRec, CoindRec m₁ m₂ ∧ ∀ m₁' m₂', CoindRec m₁' m₂' → SameFinite Ret CoindRec m₁' m₂'

/-- `m` is related to itself, with equal results. `Same` is only a partial equivalence: a machine
whose visible behavior or result depends on a branch's response is not even related to itself. -/
def Deterministic (m : CoFree E N A) : Prop :=
  Same Eq m m

end CoFree
