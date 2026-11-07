import ITree.Bisim
import ITree.Outcome

universe u

namespace CoFree

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A B : Type u}

inductive SkipFinite (extra : E.Op → Prop) (bad : A → Prop) (Ret : A → B → Prop)
    (R : CoFree E N A → CoFree E N B → Prop) : CoFree E N A → CoFree E N B → Prop
  | step {m₁ m₂} : StepRel (OpRel.eq E) Ret R m₁.observe m₂.observe →
      SkipFinite extra bad Ret R m₁ m₂
  | silentL {m₁ m₁' m₂} : m₁.observe = .silent m₁' → SkipFinite extra bad Ret R m₁' m₂ →
      SkipFinite extra bad Ret R m₁ m₂
  | extraL {m₁ m₂} (op : E.Op) {k} : m₁.observe = .impure op k → extra op →
      (∀ r, SkipFinite extra bad Ret R (k r) m₂) → SkipFinite extra bad Ret R m₁ m₂
  | badL {m₁ m₂} (a : A) : m₁.observe = .pure a → bad a → SkipFinite extra bad Ret R m₁ m₂

def Skip (extra : E.Op → Prop) (bad : A → Prop) (Ret : A → B → Prop) (m₁ : CoFree E N A)
    (m₂ : CoFree E N B) : Prop :=
  ∃ R, R m₁ m₂ ∧ ∀ x y, R x y → SkipFinite extra bad Ret R x y

def NoBad (bad : A → Prop) (m : CoFree E N A) : Prop :=
  ∀ a, bad a → ¬HasOutcome m (.res a)

def HandledExtra {F : Effect.{u}} {M : NonDeterminism.{u}} {σ X : Type u} (extra : F.Op → Prop)
    (bad : B → Prop) (st : σ) : Step F M B (σ × X) → Prop
  | .silent q => q.1 = st
  | .pure b => bad b
  | .impure op k => extra op ∧ ∀ r, (k r).1 = st
  | .branch _ _ => False

def recExtra {I O : Type u} (extra : E.Op → Prop) : (Effect.Rec I O E).Op → Prop
  | .inl _ => False
  | .inr op => extra op

end CoFree
