import Lint.BinderScope
universe u w

/-- Operations `Op` with their responses `Resp`, and branches `BrOp` with theirs `BrResp`.
An operation is answered by whoever runs or handles the program. A branch is a choice the
program does not control and nobody handles: handlers pass it through, and equivalence
(`CoFree.Same`) requires every response to behave the same. Without branches by default.

Every branch has a response: a branch with none would be a silent step leading nowhere, which
`CoFree.Same` would relate to every machine. A semantics that gets stuck emits undefined
behavior instead. -/
structure Effect : Type (u+1) where
  Op : Type u
  Resp : Op → Type u
  BrOp : Type u := PEmpty
  BrResp : BrOp → Type u := fun _ => PEmpty
  brResp_nonempty : ∀ c, Nonempty (BrResp c) := by
    first | exact fun _ => inferInstance | exact nofun

namespace Effect

abbrev sum (E F : Effect.{u}) : Effect.{u} where
  Op := E.Op ⊕ F.Op
  Resp
    | .inl op => E.Resp op
    | .inr op => F.Resp op
  BrOp := E.BrOp ⊕ F.BrOp
  BrResp
    | .inl c => E.BrResp c
    | .inr c => F.BrResp c
  brResp_nonempty
    | .inl c => E.brResp_nonempty c
    | .inr c => F.brResp_nonempty c

infixr:65 " ⊕ₑ " => Effect.sum

abbrev lift (E : Effect.{u}) : Effect.{max u w} where
  Op := ULift E.Op
  Resp op := ULift (E.Resp op.down)
  BrOp := ULift E.BrOp
  BrResp c := ULift (E.BrResp c.down)
  brResp_nonempty c := let ⟨r⟩ := E.brResp_nonempty c.down; ⟨⟨r⟩⟩

abbrev Call (I O : Type u) : Effect.{u} where
  Op := I
  Resp _ := O

/-- Operations of a recursive program: calls `.inl i` returning `O`, and operations of `E`. -/
abbrev Rec (I O : Type u) (E : Effect.{u}) : Effect.{u} :=
  Call I O ⊕ₑ E

/-- How the branches of `E` are branches of `F`, for passing them through a handler or a
renaming: the branch `c` becomes `op c`, whose responses come back through `resp`. -/
structure BrMap (E F : Effect.{u}) : Type u where
  op : E.BrOp → F.BrOp
  resp : (c : E.BrOp) → F.BrResp (op c) → E.BrResp c

namespace BrMap

variable {E F G : Effect.{u}}

def id : BrMap E E := ⟨fun c => c, fun _ r => r⟩

def inl : BrMap E (E ⊕ₑ F) := ⟨Sum.inl, fun _ r => r⟩

def inr : BrMap F (E ⊕ₑ F) := ⟨Sum.inr, fun _ r => r⟩

def sum (b₁ : BrMap E G) (b₂ : BrMap F G) : BrMap (E ⊕ₑ F) G where
  op
    | .inl c => b₁.op c
    | .inr c => b₂.op c
  resp
    | .inl c => b₁.resp c
    | .inr c => b₂.resp c

/-- `E` has no branches. -/
def empty (h : E.BrOp → False) : BrMap E F :=
  ⟨fun c => (h c).elim, fun c => (h c).elim⟩

end BrMap

end Effect
