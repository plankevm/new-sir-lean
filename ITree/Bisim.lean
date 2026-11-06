import ITree.Program

universe u

namespace CoFree

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A B : Type u}

structure OpRel (E : Effect.{u}) where
  op : E.Op → E.Op → Prop
  resp : (o₁ o₂ : E.Op) → E.Resp o₁ → E.Resp o₂ → Prop

def OpRel.eq (E : Effect.{u}) : OpRel E := ⟨Eq, fun _ _ r₁ r₂ => HEq r₁ r₂⟩

def OpRel.calls {I O : Type u} (RI : I → I → Prop) (ρ : OpRel E) : OpRel (Effect.Rec I O E) where
  op
    | .inl i₁, .inl i₂ => RI i₁ i₂
    | .inr o₁, .inr o₂ => ρ.op o₁ o₂
    | _, _ => False
  resp
    | .inl _, .inl _ => fun r₁ r₂ => r₁ = r₂
    | .inr o₁, .inr o₂ => ρ.resp o₁ o₂
    | _, _ => fun _ _ => False

def StepRel (ρ : OpRel E) (Ret : A → B → Prop) (R : CoFree E N A → CoFree E N B → Prop) :
    Step E N A (CoFree E N A) → Step E N B (CoFree E N B) → Prop
  | .pure a, .pure b => Ret a b
  | .silent m₁, .silent m₂ => R m₁ m₂
  | .impure o₁ k₁, .impure o₂ k₂ => ρ.op o₁ o₂ ∧ ∀ r₁ r₂, ρ.resp o₁ o₂ r₁ r₂ → R (k₁ r₁) (k₂ r₂)
  | .branch c₁ k₁, .branch c₂ k₂ => c₁ = c₂ ∧ ∀ r₁ r₂, HEq r₁ r₂ → R (k₁ r₁) (k₂ r₂)
  | _, _ => False

def Bisim (ρ : OpRel E) (Ret : A → B → Prop) (m₁ : CoFree E N A) (m₂ : CoFree E N B) : Prop :=
  ∃ R : CoFree E N A → CoFree E N B → Prop, R m₁ m₂ ∧ ∀ x y, R x y → StepRel ρ Ret R x.observe y.observe

def IterRel {S₁ S₂ : Type u} (RS : S₁ → S₂ → Prop) (Ret : A → B → Prop) :
    IterStep S₁ A → IterStep S₂ B → Prop
  | .repeat s₁, .repeat s₂ => RS s₁ s₂
  | .exit a, .exit b => Ret a b
  | _, _ => False

def ForInRel {β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) : ForInStep β₁ → ForInStep β₂ → Prop
  | .yield b₁, .yield b₂ => RB b₁ b₂
  | .done b₁, .done b₂ => RB b₁ b₂
  | _, _ => False

def LoopRel {β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) (Ret : β₁ → β₂ → Prop) :
    ForInStep β₁ → ForInStep β₂ → Prop
  | .yield b₁, .yield b₂ => RB b₁ b₂
  | .done b₁, .done b₂ => Ret b₁ b₂
  | _, _ => False

end CoFree
