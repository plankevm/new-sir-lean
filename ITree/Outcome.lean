import ITree.Machine

universe u w

variable {N : NonDeterminism.{u}} {E : Effect.{u}} {A : Type u}

namespace CoFree

inductive Outcome (E : Effect.{u}) (A : Type u) : Type u
  | res (value : A)
  | terminalOp (op : E.Op)

inductive HasOutcome : CoFree E N A → Outcome E A → Prop
  | res {m v} : m.observe = .pure v → HasOutcome m (.res v)
  | terminal {m op} : (E.Resp op → False) → (∃ k, m.observe = .impure op k) → HasOutcome m (.terminalOp op)
  | silent {m m' o} : HasOutcome m' o → m.observe = .silent m' → HasOutcome m o
  | branch {m m' o} : HasOutcome m' o → (∃ br k, m.observe = .branch br k ∧ ∃ r, k r = m') → HasOutcome m o
  | impure {m m' o} : HasOutcome m' o → (∃ op k, m.observe = .impure op k ∧ ∃ r, k r = m') → HasOutcome m o

abbrev HasResOutcome (m : CoFree E N A) (value : A) : Prop := HasOutcome m (.res value)
abbrev HasTerminalOpOutcome (m : CoFree E N A) (op : E.Op) : Prop := HasOutcome m (.terminalOp op)

end CoFree
