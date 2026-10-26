import ITree.Machine

universe u

namespace CoFree

variable {E : Effect.{u}} {A : Type u}

/-- `m` returns `a` for some answers to its operations and some responses to its branches, after
finitely many steps. -/
inductive Returns : CoFree E A → A → Prop
  | pure {m a} : m.observe = .pure a → Returns m a
  | silent {m m' a} : m.observe = .silent m' → Returns m' a → Returns m a
  | impure {m op k a} (r : E.Resp op) : m.observe = .impure op k → Returns (k r) a → Returns m a
  | branch {m c k a} (r : E.BrResp c) : m.observe = .branch c k → Returns (k r) a → Returns m a

end CoFree
