import Lint.BinderScope
universe u w

/-- Operations `Op` with their responses `Resp`, answered by whoever runs or handles the program. -/
structure Effect : Type (u+1) where
  Op : Type u
  Resp : Op → Type u

/-- Choices `Op` with their responses `Resp`: choices the program does not control and nobody
handles. Handlers pass them through, and equivalence (`CoFree.Same`) treats them as unobserved
steps that must behave the same for every response. Without choices by default.

Every choice has a response: a choice with none would be a silent step leading nowhere, which
`CoFree.Same` would relate to every machine. A semantics that gets stuck emits undefined
behavior instead.

Lives in the same universe as `Effect`: a machine's states must hold its choices' responses. -/
structure NonDeterminism : Type (u+1) where
  Op : Type u := PEmpty
  Resp : Op → Type u := fun _ => PEmpty
  resp_nonempty : ∀ c, Nonempty (Resp c) := by
    first | exact fun _ => inferInstance | exact nofun

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

namespace NonDeterminism

/-- No choices. -/
abbrev none : NonDeterminism.{u} := {}

abbrev sum (N M : NonDeterminism.{u}) : NonDeterminism.{u} where
  Op := N.Op ⊕ M.Op
  Resp
    | .inl c => N.Resp c
    | .inr c => M.Resp c
  resp_nonempty
    | .inl c => N.resp_nonempty c
    | .inr c => M.resp_nonempty c

infixr:65 " ⊕ₙ " => NonDeterminism.sum

abbrev lift (N : NonDeterminism.{u}) : NonDeterminism.{max u w} where
  Op := ULift N.Op
  Resp c := ULift (N.Resp c.down)
  resp_nonempty c := let ⟨r⟩ := N.resp_nonempty c.down; ⟨⟨r⟩⟩

/-- How the choices of `N` are choices of `M`, for passing them through a handler or a renaming:
the choice `c` becomes `op c`, whose responses come back through `resp`. -/
structure Map (N M : NonDeterminism.{u}) : Type u where
  op : N.Op → M.Op
  resp : (c : N.Op) → M.Resp (op c) → N.Resp c

namespace Map

variable {N M L : NonDeterminism.{u}}

def id : Map N N := ⟨fun c => c, fun _ r => r⟩

def inl : Map N (N ⊕ₙ M) := ⟨Sum.inl, fun _ r => r⟩

def inr : Map M (N ⊕ₙ M) := ⟨Sum.inr, fun _ r => r⟩

def sum (b₁ : Map N L) (b₂ : Map M L) : Map (N ⊕ₙ M) L where
  op
    | .inl c => b₁.op c
    | .inr c => b₂.op c
  resp
    | .inl c => b₁.resp c
    | .inr c => b₂.resp c

/-- `N` has no choices. -/
def empty (h : N.Op → False) : Map N M :=
  ⟨fun c => (h c).elim, fun c => (h c).elim⟩

end Map

end NonDeterminism
