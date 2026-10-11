import ITree.Machine

/-! Weak bisimulation with hidden operations and undefined behavior.

`Same hidden ub RR m₁ m₂`: the two machines perform the same visible operations in the same
order and return values related by `RR`, or both reach undefined behavior, ignoring finitely
many silent steps on either side at a time. A machine that runs silently forever is related
only to another such machine.

A silent step is a `silent` node, or an operation satisfying `hidden` with at least one possible
answer. Hidden operations are answered on each side independently, and the two sides must
agree for every pair of answers: they model a choice the environment makes that the program
may not depend on (in SIR, where an allocation is placed). So `Same` is a partial equivalence,
not an equivalence: a program whose visible behavior depends on a hidden answer is not related
to itself. `Deterministic`-style statements are written `Same hidden ub Eq m m`.

Operations satisfying `ub` are terminal: they relate to every other `ub` operation and to
nothing else, whatever the operations are (their arguments may depend on hidden answers).

With no hidden operations and no undefined behavior, `Same` is the usual weak bisimulation
(`Eutt`), and is reflexive. -/

universe u

namespace CoFree

variable {E : Effect.{u}} {A B : Type u}

/-- `n` is what `m` continues as after a silent step: a `silent` node, or a hidden operation
with any of its answers. -/
def Next (hidden : E.Op → Prop) (m n : CoFree E A) : Prop :=
  m.observe = .silent n ∨
    ∃ op, hidden op ∧ ∃ k : E.Resp op → CoFree E A, m.observe = .impure op k ∧ ∃ r, k r = n

/-- `m` takes a silent step. A hidden operation without any possible answer does not: it is
stuck, so it relates to nothing. -/
def Silent (hidden : E.Op → Prop) (m : CoFree E A) : Prop :=
  ∃ n, Next hidden m n

/-- One layer of `Same`. `silent`, `impure` and `ub` progress through `R`; `silentL` and
`silentR` stay in `SameF`, so they can skip only finitely many silent steps in a row. -/
inductive SameF (hidden ub : E.Op → Prop) (RR : A → B → Prop)
    (R : CoFree E A → CoFree E B → Prop) : CoFree E A → CoFree E B → Prop
  | silent {m₁ m₂} : Silent hidden m₁ → Silent hidden m₂ →
      (∀ n₁ n₂, Next hidden m₁ n₁ → Next hidden m₂ n₂ → R n₁ n₂) → SameF hidden ub RR R m₁ m₂
  | impure {m₁ m₂} (op : E.Op) {k₁ k₂} : m₁.observe = .impure op k₁ →
      m₂.observe = .impure op k₂ → ¬hidden op → (∀ r, R (k₁ r) (k₂ r)) →
      SameF hidden ub RR R m₁ m₂
  | ret {m₁ m₂ a b} : m₁.observe = .pure a → m₂.observe = .pure b → RR a b →
      SameF hidden ub RR R m₁ m₂
  | ub {m₁ m₂} (op₁ op₂ : E.Op) {k₁ k₂} : m₁.observe = .impure op₁ k₁ →
      m₂.observe = .impure op₂ k₂ → ub op₁ → ub op₂ → ¬hidden op₁ → ¬hidden op₂ →
      SameF hidden ub RR R m₁ m₂
  | silentL {m₁ m₂} : Silent hidden m₁ → (∀ n, Next hidden m₁ n → SameF hidden ub RR R n m₂) →
      SameF hidden ub RR R m₁ m₂
  | silentR {m₁ m₂} : Silent hidden m₂ → (∀ n, Next hidden m₂ n → SameF hidden ub RR R m₁ n) →
      SameF hidden ub RR R m₁ m₂

def IsSame (hidden ub : E.Op → Prop) (RR : A → B → Prop)
    (R : CoFree E A → CoFree E B → Prop) : Prop :=
  ∀ m₁ m₂, R m₁ m₂ → SameF hidden ub RR R m₁ m₂

/-- The greatest fixed point of `SameF`. -/
def Same (hidden ub : E.Op → Prop) (RR : A → B → Prop) (m₁ : CoFree E A) (m₂ : CoFree E B) :
    Prop :=
  ∃ R, IsSame hidden ub RR R ∧ R m₁ m₂

/-- Weak bisimulation: `Same` without hidden operations or undefined behavior. -/
def Eutt (RR : A → B → Prop) (m₁ : CoFree E A) (m₂ : CoFree E B) : Prop :=
  Same (fun _ => False) (fun _ => False) RR m₁ m₂

/-- Pairs reachable from `R` by finitely many layers of `SameF`, or already in `Same`: the
relation `Same.coind` lets a coinductive proof step to. -/
inductive SameSteps (hidden ub : E.Op → Prop) (RR : A → B → Prop)
    (R : CoFree E A → CoFree E B → Prop) : CoFree E A → CoFree E B → Prop
  | done {m₁ m₂} : Same hidden ub RR m₁ m₂ → SameSteps hidden ub RR R m₁ m₂
  | step {m₁ m₂} : SameF hidden ub RR (SameSteps hidden ub RR R) m₁ m₂ →
      SameSteps hidden ub RR R m₁ m₂
  | recur {m₁ m₂} : R m₁ m₂ → SameSteps hidden ub RR R m₁ m₂

end CoFree
