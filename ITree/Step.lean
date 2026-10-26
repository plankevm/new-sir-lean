import ITree.Effect

universe u w₁ w₂

inductive Step (E : Effect.{u}) (A : Type u) (S : Type w₁) : Type (max u w₁) where
  | pure (value : A)
  | silent (next : S)
  | impure (op : E.Op) (next : E.Resp op → S)
  | branch (c : E.BrOp) (next : E.BrResp c → S)

namespace Step

variable {E : Effect.{u}} {A : Type u}

def map {S : Type w₁} {T : Type w₂} (f : S → T) : Step E A S → Step E A T
  | .pure a => .pure a
  | .silent s => .silent (f s)
  | .impure op k => .impure op (f ∘ k)
  | .branch c k => .branch c (f ∘ k)

end Step
