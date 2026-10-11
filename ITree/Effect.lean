universe u w

structure Effect : Type (u+1) where
  Op : Type u
  Resp : Op → Type u

namespace Effect

abbrev sum (E F : Effect.{u}) : Effect.{u} where
  Op := E.Op ⊕ F.Op
  Resp
    | .inl op => E.Resp op
    | .inr op => F.Resp op

infixr:65 " ⊕ₑ " => Effect.sum

abbrev lift (E : Effect.{u}) : Effect.{max u w} where
  Op := ULift E.Op
  Resp op := ULift (E.Resp op.down)

abbrev Call (I O : Type u) : Effect.{u} where
  Op := I
  Resp _ := O

/-- Operations of a recursive program: calls `.inl i` returning `O`, and operations of `E`. -/
abbrev Rec (I O : Type u) (E : Effect.{u}) : Effect.{u} :=
  Call I O ⊕ₑ E

end Effect
