import ITree.Machine

/-! Weak bisimulation with branches and undefined behavior.

`Same ub RR m₁ m₂`: the two machines perform the same operations in the same order and return
values related by `RR`, or both reach undefined behavior, ignoring finitely many silent steps on
either side at a time. A machine that runs silently forever is related only to another such
machine.

A silent step is a `silent` node or a `br` node. A branch is taken with each of its responses,
on each side independently, and the two sides must agree for every pair of responses: it models
a choice the environment makes that the program may not depend on (in SIR, where an allocation
is placed). So `Same` is a partial equivalence, not an equivalence: a program whose visible
behavior depends on a branch's response is not related to itself. `Deterministic`-style
statements are written `Same ub Eq m m`, and say that every branch behaves the same.

Every branch has a response (`Effect.brResp_nonempty`); a branch with none would be vacuously
related to every machine.

Operations satisfying `ub` are terminal: they relate to every other `ub` operation and to
nothing else, whatever the operations are (their arguments may depend on branch responses).

With no undefined behavior and no branches, `Same` is the usual weak bisimulation (`Eutt`), and
is reflexive. -/

universe u

namespace CoFree

variable {E : Effect.{u}} {A B : Type u}

/-- `n` is what `m` continues as after a silent step: a `silent` node, or a branch with any of
its responses. -/
def Next (m n : CoFree E A) : Prop :=
  m.observe = .silent n ∨ ∃ c, ∃ k : E.BrResp c → CoFree E A, m.observe = .br c k ∧ ∃ r, k r = n

/-- `m` takes a silent step. -/
def Silent (m : CoFree E A) : Prop :=
  (∃ n, m.observe = .silent n) ∨ ∃ c, ∃ k : E.BrResp c → CoFree E A, m.observe = .br c k

/-- One layer of `Same`. `silent`, `impure` and `ub` progress through `R`; `silentL` and
`silentR` stay in `SameF`, so they can skip only finitely many silent steps in a row. -/
inductive SameF (ub : E.Op → Prop) (RR : A → B → Prop)
    (R : CoFree E A → CoFree E B → Prop) : CoFree E A → CoFree E B → Prop
  | silent {m₁ m₂} : Silent m₁ → Silent m₂ →
      (∀ n₁ n₂, Next m₁ n₁ → Next m₂ n₂ → R n₁ n₂) → SameF ub RR R m₁ m₂
  | impure {m₁ m₂} (op : E.Op) {k₁ k₂} : m₁.observe = .impure op k₁ →
      m₂.observe = .impure op k₂ → (∀ r, R (k₁ r) (k₂ r)) → SameF ub RR R m₁ m₂
  | ret {m₁ m₂ a b} : m₁.observe = .pure a → m₂.observe = .pure b → RR a b →
      SameF ub RR R m₁ m₂
  | ub {m₁ m₂} (op₁ op₂ : E.Op) {k₁ k₂} : m₁.observe = .impure op₁ k₁ →
      m₂.observe = .impure op₂ k₂ → ub op₁ → ub op₂ → SameF ub RR R m₁ m₂
  | silentL {m₁ m₂} : Silent m₁ → (∀ n, Next m₁ n → SameF ub RR R n m₂) → SameF ub RR R m₁ m₂
  | silentR {m₁ m₂} : Silent m₂ → (∀ n, Next m₂ n → SameF ub RR R m₁ n) → SameF ub RR R m₁ m₂

def IsSame (ub : E.Op → Prop) (RR : A → B → Prop) (R : CoFree E A → CoFree E B → Prop) :
    Prop :=
  ∀ m₁ m₂, R m₁ m₂ → SameF ub RR R m₁ m₂

/-- The greatest fixed point of `SameF`. -/
def Same (ub : E.Op → Prop) (RR : A → B → Prop) (m₁ : CoFree E A) (m₂ : CoFree E B) : Prop :=
  ∃ R, IsSame ub RR R ∧ R m₁ m₂

/-- Weak bisimulation: `Same` without undefined behavior. -/
def Eutt (RR : A → B → Prop) (m₁ : CoFree E A) (m₂ : CoFree E B) : Prop :=
  Same (fun _ => False) RR m₁ m₂

/-- Pairs reachable from `R` by finitely many layers of `SameF`, or already in `Same`: the
relation `Same.coind` lets a coinductive proof step to. -/
inductive SameSteps (ub : E.Op → Prop) (RR : A → B → Prop)
    (R : CoFree E A → CoFree E B → Prop) : CoFree E A → CoFree E B → Prop
  | done {m₁ m₂} : Same ub RR m₁ m₂ → SameSteps ub RR R m₁ m₂
  | step {m₁ m₂} : SameF ub RR (SameSteps ub RR R) m₁ m₂ → SameSteps ub RR R m₁ m₂
  | recur {m₁ m₂} : R m₁ m₂ → SameSteps ub RR R m₁ m₂

end CoFree
