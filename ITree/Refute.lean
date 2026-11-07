import ITree.Same

universe u

namespace CoFree

variable {E : Effect.{u}} {N N₁ N₂ : NonDeterminism.{u}} {A B : Type u}

def UStep (m m' : CoFree E N A) : Prop :=
  m.observe = .silent m' ∨ ∃ c k r, m.observe = .branch c k ∧ k r = m'

def Visible (m : CoFree E N A) : Prop := ¬ForallUnobserved m fun _ => True

def Chain (f : Nat → CoFree E N A) : Prop := ∀ n, UStep (f n) (f (n + 1))

def VisMatch (m₁ : CoFree E N₁ A) (m₂ : CoFree E N₂ B) : Prop :=
  (∃ a b, m₁.observe = .pure a ∧ m₂.observe = .pure b) ∨
  ∃ op k₁ k₂, m₁.observe = .impure op k₁ ∧ m₂.observe = .impure op k₂

inductive Bad (Ret : A → B → Prop) : CoFree E N₁ A → CoFree E N₂ B → Prop
  | ret {m₁ m₂} (a : A) (b : B) : m₁.observe = .pure a → m₂.observe = .pure b → ¬Ret a b →
      Bad Ret m₁ m₂
  | mismatch {m₁ m₂} : Visible m₁ → Visible m₂ → ¬VisMatch m₁ m₂ → Bad Ret m₁ m₂
  | impure {m₁ m₂} (op : E.Op) {k₁ k₂} (r : E.Resp op) : m₁.observe = .impure op k₁ →
      m₂.observe = .impure op k₂ → Bad Ret (k₁ r) (k₂ r) → Bad Ret m₁ m₂
  | both {m₁ m₁' m₂ m₂'} : UStep m₁ m₁' → UStep m₂ m₂' → Bad Ret m₁' m₂' → Bad Ret m₁ m₂
  | left {m₁ m₁' m₂} : UStep m₁ m₁' → Visible m₂ → Bad Ret m₁' m₂ → Bad Ret m₁ m₂
  | right {m₁ m₂ m₂'} : Visible m₁ → UStep m₂ m₂' → Bad Ret m₁ m₂' → Bad Ret m₁ m₂
  | divL {m₁ m₂} (f : Nat → CoFree E N₁ A) : Chain f → f 0 = m₁ → Visible m₂ → Bad Ret m₁ m₂
  | divR {m₁ m₂} (f : Nat → CoFree E N₂ B) : Visible m₁ → Chain f → f 0 = m₂ → Bad Ret m₁ m₂

end CoFree
