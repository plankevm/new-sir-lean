import ITree.Effect

universe u w₁ w₂

inductive Step (E : Effect.{u}) (N : NonDeterminism.{u}) (A : Type u) (S : Type w₁) :
    Type (max u w₁) where
  | pure (value : A)
  | silent (next : S)
  | impure (op : E.Op) (next : E.Resp op → S)
  | branch (c : N.Op) (next : N.Resp c → S)

namespace Step

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u}

def map {S : Type w₁} {T : Type w₂} (f : S → T) : Step E N A S → Step E N A T
  | .pure a => .pure a
  | .silent s => .silent (f s)
  | .impure op k => .impure op (f ∘ k)
  | .branch c k => .branch c (f ∘ k)

end Step
