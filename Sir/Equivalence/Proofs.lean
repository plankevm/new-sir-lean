import Sir.Equivalence

open CoFree

namespace Sir.Proofs

lemma definedAnd_symm {α : Type} {r r' : α → α → Prop} (hr : ∀ a b, r a b → r' b a)
    {a b : UB ⊕ α} : DefinedAnd r a b → DefinedAnd r' b a := by
  rcases a with _ | a <;> rcases b with _ | b <;> simp only [DefinedAnd, imp_self]
  exact hr a b

lemma definedAnd_trans {α : Type} {r₁ r₂ r₃ : α → α → Prop}
    (hr : ∀ a b c, r₁ a b → r₂ b c → r₃ a c) {a b c : UB ⊕ α} :
    DefinedAnd r₁ a b → DefinedAnd r₂ b c → DefinedAnd r₃ a c := by
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;>
    simp only [DefinedAnd, false_imp_iff, imp_false, not_false_eq_true, implies_true]
  exact hr a b c

lemma mainEquiv_symm {p₁ p₂ : Program} {l₁ : Layout p₁} {l₂ : Layout p₂}
    {imms₁ : MainImmutablesMap p₁} {imms₂ : MainImmutablesMap p₂}
    (h : MainEquiv l₁ l₂ imms₁ imms₂) : MainEquiv l₂ l₁ imms₂ imms₁ :=
  fun static calldata e w₀ =>
    Same.mono (fun _ _ => definedAnd_symm fun _ _ => Eq.symm) (Same.symm (h static calldata e w₀))

lemma mainEquiv_trans {p₁ p₂ p₃ : Program} {l₁ : Layout p₁} {l₂ : Layout p₂} {l₃ : Layout p₃}
    {imms₁ : MainImmutablesMap p₁} {imms₂ : MainImmutablesMap p₂} {imms₃ : MainImmutablesMap p₃}
    (h₁ : MainEquiv l₁ l₂ imms₁ imms₂) (h₂ : MainEquiv l₂ l₃ imms₂ imms₃) :
    MainEquiv l₁ l₃ imms₁ imms₃ :=
  fun static calldata e w₀ =>
    Same.mono (fun _ _ ⟨_, hab, hbc⟩ => definedAnd_trans (r₁ := Eq) (r₂ := Eq) (fun _ _ _ => Eq.trans) hab hbc)
      (Same.trans (h₁ static calldata e w₀) (h₂ static calldata e w₀))

lemma deployOutcomeEquiv_symm {p₁ p₂ : Program} {l₁ : Layout p₁} {l₂ : Layout p₂}
    {a b : InitOutcome} :
    DeployOutcomeEquiv l₁ l₂ a b → DeployOutcomeEquiv l₂ l₁ b a := by
  intro h
  rcases a with ⟨q₁, m₁, s₁⟩ | _ | _ | _ <;>
    rcases b with ⟨q₂, m₂, s₂⟩ | _ | _ | _ <;>
    simp only [DeployOutcomeEquiv] at h ⊢
  all_goals first
    | (obtain ⟨rfl, rfl, rfl, h⟩ := h; exact ⟨rfl, rfl, rfl, mainEquiv_symm h⟩)
    | simp_all [eq_comm]

lemma deployOutcomeEquiv_trans {p₁ p₂ p₃ : Program} {l₁ : Layout p₁} {l₂ : Layout p₂}
    {l₃ : Layout p₃} {a b c : InitOutcome} :
    DeployOutcomeEquiv l₁ l₂ a b → DeployOutcomeEquiv l₂ l₃ b c →
      DeployOutcomeEquiv l₁ l₃ a c := by
  intro h₁ h₂
  rcases a with ⟨q₁, m₁, s₁⟩ | _ | _ | _ <;>
    rcases b with ⟨q₂, m₂, s₂⟩ | _ | _ | _ <;>
    rcases c with ⟨q₃, m₃, s₃⟩ | _ | _ | _ <;>
    simp only [DeployOutcomeEquiv] at h₁ h₂ ⊢
  all_goals first
    | (obtain ⟨rfl, rfl, rfl, h₁⟩ := h₁
       obtain ⟨rfl, _, rfl, h₂⟩ := h₂
       exact ⟨rfl, rfl, rfl, mainEquiv_trans h₁ h₂⟩)
    | simp_all

lemma equiv_symm {p₁ p₂ : Program} (h : Equiv p₁ p₂) : Equiv p₂ p₁ :=
  ⟨h.1.symm, fun l₁ l₂ e c w₀ hu =>
    Same.mono (fun _ _ => definedAnd_symm (r := DeployOutcomeEquiv l₂ l₁) fun _ _ => deployOutcomeEquiv_symm)
      (Same.symm (h.2 l₂ l₁ e c w₀ hu))⟩

lemma equiv_trans {p₁ p₂ p₃ : Program} (h₁ : Equiv p₁ p₂) (h₂ : Equiv p₂ p₃) :
    Equiv p₁ p₃ := by
  refine ⟨h₁.1.trans h₂.1, fun l₁ l₃ e c w₀ hu => ?_⟩
  obtain ⟨l₂⟩ := h₁.1.mp ⟨l₁⟩
  exact Same.mono (fun _ _ ⟨_, hab, hbc⟩ => definedAnd_trans (r₁ := DeployOutcomeEquiv l₁ l₂)
      (r₂ := DeployOutcomeEquiv l₂ l₃) (fun _ _ _ => deployOutcomeEquiv_trans) hab hbc)
    (Same.trans (h₁.2 l₁ l₂ e c w₀ hu) (h₂.2 l₂ l₃ e c w₀ hu))

lemma equiv_refl_left {p₁ p₂ : Program} (h : Equiv p₁ p₂) : Equiv p₁ p₁ :=
  equiv_trans h (equiv_symm h)

end Sir.Proofs
