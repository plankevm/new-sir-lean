

structure NatRange where
  start : Nat
  size : Nat
  deriving DecidableEq

namespace NatRange

def «end» (a : NatRange) : Nat := a.start + a.size

def Disjoint (a₁ a₂ : NatRange) : Prop := a₁.end ≤ a₂.start ∨ a₂.end ≤ a₁.start

theorem Disjoint_imp_no_overlap : ∀ a₁ a₂, (Disjoint a₁ a₂) → (¬∃ x, a₁.start ≤ x ∧ x < a₁.end ∧
a₂.start ≤ x ∧ x < a₂.end) := by
  unfold Disjoint
  intro disjoint
  grind

theorem no_overlap_imp_Disjoint_or_empty :
  ∀ a₁ a₂, (¬∃ x, a₁.start ≤ x ∧ x < a₁.end ∧ a₂.start ≤ x ∧ x < a₂.end) →
    (Disjoint a₁ a₂ ∨ a₁.size = 0 ∨ a₂.size = 0) := by
  unfold Disjoint
  intro a₁ a₂ no_overlap
  refine Classical.byContradiction fun h => ?_
  exact no_overlap ⟨max a₁.start a₂.start, by simp only [NatRange.end] at *; omega⟩

instance {a₁ a₂ : NatRange} : Decidable (a₁.Disjoint a₂) := by unfold Disjoint; infer_instance

end NatRange
