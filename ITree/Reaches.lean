import ITree.Machine

universe u

namespace CoFree

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u}

inductive Reaches : CoFree E N A → CoFree E N A → Prop
  | refl (m : CoFree E N A) : Reaches m m
  | silent {m m' m''} : m.observe = .silent m' → Reaches m' m'' → Reaches m m''
  | impure {m op k m''} (r : E.Resp op) : m.observe = .impure op k → Reaches (k r) m'' → Reaches m m''
  | branch {m c k m''} (r : N.Resp c) : m.observe = .branch c k → Reaches (k r) m'' → Reaches m m''

end CoFree
