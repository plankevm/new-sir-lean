import ITree.Reaches.Proofs

universe u

namespace CoFree

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A B : Type u}

theorem observe_interp {σ : Type u} (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X)) :
    ∀ (st : σ) (m : CoFree E N A),
      (interp h st m).observe = (h st (m.step m.initial)).map fun
        | (st', .inl s') => interp h st' (m.startAt s')
        | (st', .inr j) => interp h st' (m.target j) :=
  Proofs.observe_interp h

theorem interp_reaches {σ : Type u} (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X))
    (I : σ → Prop)
    (hsilent : ∀ {X : Type u} st (s : Step E N A X) x, I st → h st s = .silent x → I x.1)
    (himpure : ∀ {X : Type u} st (s : Step E N A X) op k r, I st → h st s = .impure op k → I (k r).1)
    (hbranch : ∀ {X : Type u} st (s : Step E N A X) c k r, I st → h st s = .branch c k → I (k r).1) :
    ∀ (st : σ) (m : CoFree E N A) (m' : CoFree F M B),
      I st → Reaches (interp h st m) m' → ∃ st' m₀, I st' ∧ m' = interp h st' m₀ :=
  Proofs.interp_reaches h I hsilent himpure hbranch

theorem reaches_of_observe_eq :
    ∀ {m₁ m₂ m' : CoFree E N A}, m₁.observe = m₂.observe → Reaches m₁ m' → m' = m₁ ∨ Reaches m₂ m' :=
  Proofs.reaches_of_observe_eq

end CoFree
