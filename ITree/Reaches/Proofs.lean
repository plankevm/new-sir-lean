import ITree.Reaches
import ITree.Machine.Theorems
import ITree.Step.Theorems

universe u

namespace CoFree.Proofs

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A B : Type u}

lemma observe_interp {σ : Type u} (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X))
    (st : σ) (m : CoFree E N A) :
    (interp h st m).observe = (h st (m.step m.initial)).map fun
      | (st', .inl s') => interp h st' (m.startAt s')
      | (st', .inr j) => interp h st' (m.target j) := by
  obtain ⟨S, J, s₀, step, target⟩ := m
  simp only [interp, observe, Step.map_map]
  refine Step.map_congr (fun x => ?_) _
  rcases x with ⟨st', s' | j⟩ <;> rfl

theorem interp_reaches {σ : Type u} (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X))
    (I : σ → Prop)
    (hsilent : ∀ {X : Type u} st (s : Step E N A X) x, I st → h st s = .silent x → I x.1)
    (himpure : ∀ {X : Type u} st (s : Step E N A X) op k r, I st → h st s = .impure op k → I (k r).1)
    (hbranch : ∀ {X : Type u} st (s : Step E N A X) c k r, I st → h st s = .branch c k → I (k r).1)
    (st : σ) (m : CoFree E N A) (m' : CoFree F M B) (hI : I st) (hr : Reaches (interp h st m) m') :
    ∃ st' m₀, I st' ∧ m' = interp h st' m₀ := by
  generalize hM : interp h st m = M at hr
  induction hr generalizing st m with
  | refl => exact ⟨st, m, hI, hM.symm⟩
  | @silent M M' M'' ho _ ih =>
    subst hM
    rw [observe_interp] at ho
    generalize hs : h st (m.step m.initial) = s at ho
    rcases s with _ | x | _ | _ <;> simp only [Step.map] at ho <;> try contradiction
    injection ho with ho
    have hx := hsilent st _ x hI hs
    rcases x with ⟨st', s' | j⟩
    · exact ih st' _ hx ho
    · exact ih st' _ hx ho
  | @impure M op k M'' r ho _ ih =>
    subst hM
    rw [observe_interp] at ho
    generalize hs : h st (m.step m.initial) = s at ho
    rcases s with _ | _ | ⟨op', k'⟩ | _ <;> simp only [Step.map] at ho <;> try contradiction
    injection ho with hop hk
    subst hop
    cases hk
    have hx := himpure st _ _ k' r hI hs
    rcases hkr : k' r with ⟨st', s' | j⟩ <;> rw [hkr] at hx
    · exact ih st' (m.startAt s') hx (by rw [Function.comp_apply, hkr])
    · exact ih st' (m.target j) hx (by rw [Function.comp_apply, hkr])
  | @branch M c k M'' r ho _ ih =>
    subst hM
    rw [observe_interp] at ho
    generalize hs : h st (m.step m.initial) = s at ho
    rcases s with _ | _ | _ | ⟨c', k'⟩ <;> simp only [Step.map] at ho <;> try contradiction
    injection ho with hc hk
    subst hc
    cases hk
    have hx := hbranch st _ _ k' r hI hs
    rcases hkr : k' r with ⟨st', s' | j⟩ <;> rw [hkr] at hx
    · exact ih st' (m.startAt s') hx (by rw [Function.comp_apply, hkr])
    · exact ih st' (m.target j) hx (by rw [Function.comp_apply, hkr])

theorem reaches_of_observe_eq {m₁ m₂ m' : CoFree E N A} (ho : m₁.observe = m₂.observe)
    (hr : Reaches m₁ m') : m' = m₁ ∨ Reaches m₂ m' := by
  cases hr with
  | refl => exact .inl rfl
  | silent h hr => exact .inr (.silent (ho ▸ h) hr)
  | impure r h hr => exact .inr (.impure r (ho ▸ h) hr)
  | branch r h hr => exact .inr (.branch r (ho ▸ h) hr)

end CoFree.Proofs
