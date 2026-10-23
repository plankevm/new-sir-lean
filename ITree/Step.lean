import ITree.Effect

universe u w₁ w₂

inductive Step (E : Effect.{u}) (A : Type u) (S : Type w₁) : Type (max u w₁) where
  | pure (value : A)
  | silent (next : S)
  | impure (op : E.Op) (next : E.Resp op → S)
  | br (c : E.BrOp) (next : E.BrResp c → S)

namespace Step

variable {E : Effect.{u}} {A : Type u}

def map {S : Type w₁} {T : Type w₂} (f : S → T) : Step E A S → Step E A T
  | .pure a => .pure a
  | .silent s => .silent (f s)
  | .impure op k => .impure op fun r => f (k r)
  | .br c k => .br c fun r => f (k r)

inductive Rel {S : Type w₁} {T : Type w₂} (R : S → T → Prop) :
    Step E A S → Step E A T → Prop where
  | pure (a : A) : Rel R (.pure a) (.pure a)
  | silent {s : S} {t : T} : R s t → Rel R (.silent s) (.silent t)
  | impure (op : E.Op) {k₁ : E.Resp op → S} {k₂ : E.Resp op → T} :
      (∀ r, R (k₁ r) (k₂ r)) → Rel R (.impure op k₁) (.impure op k₂)
  | br (c : E.BrOp) {k₁ : E.BrResp c → S} {k₂ : E.BrResp c → T} :
      (∀ r, R (k₁ r) (k₂ r)) → Rel R (.br c k₁) (.br c k₂)

end Step
