import Sir.Memory

/-! The placement decision decides both ways, including sizes near `Word.size`. -/

namespace SirTests.Placement

open Sir

private def al (start size : Nat) : Allocation := ⟨Word.ofNat start, ⟨.replicate size 0⟩⟩

example : ∃ a', a'.size = 4 ∧ ValidPlacement a' [al 0 4, al 8 2] := by decide
example : ¬∃ a', a'.size = Word.size - 1 ∧ ValidPlacement a' [al 1 1] := by decide
example : (decide (∃ a', a'.size = Word.size - 2 ∧ ValidPlacement a' [al 1 1])) = true := by decide
example : (decide (∃ a', a'.size = Word.size + 1 ∧ ValidPlacement a' [])) = false := by decide

end SirTests.Placement
