import ITree.Machine

universe u w

namespace CoFree

inductive Outcome (E : Effect.{u}) (A : Type u) : Type u
  | res (value : A)
  | terminalOp (op : E.Op)

inductive HasOutcome {N : NonDeterminism.{u}} {E : Effect.{u}} {A : Type u} :
    CoFree E N A → Outcome E A → Prop
  | res {m v} : m.observe = .pure v → HasOutcome m (.res v)
  | terminal {m op} : (E.Resp op → False) → (∃ k, m.observe = .impure op k) → HasOutcome m (.terminalOp op)
  | silent {m m' o} : HasOutcome m' o → m.observe = .silent m' → HasOutcome m o
  | branch {m m' o} : HasOutcome m' o → (∃ br k, m.observe = .branch br k ∧ ∃ r, k r = m') → HasOutcome m o
  | impure {m m' o} : HasOutcome m' o → (∃ op k, m.observe = .impure op k ∧ ∃ r, k r = m') → HasOutcome m o

end CoFree
