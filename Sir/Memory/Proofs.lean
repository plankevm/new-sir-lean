import Sir.Memory

/-! `placeable` tries only 0 and the end of each live allocation. This is complete: any
placement slides down to the highest allocation end at or below it (or to 0), and stays a
placement. -/

namespace Sir.Proofs

/-- The highest end `a.1 + a.2 ≤ s` of an allocation in the list, or 0. -/
def endBelow (s : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | a :: as => if a.1 + a.2 ≤ s then max (a.1 + a.2) (endBelow s as) else endBelow s as

theorem endBelow_le (s : Nat) (l : List (Nat × Nat)) : endBelow s l ≤ s := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a as ih => simp only [endBelow]; split <;> omega

theorem le_endBelow (s : Nat) (l : List (Nat × Nat)) (a : Nat × Nat) (ha : a ∈ l)
    (hs : a.1 + a.2 ≤ s) : a.1 + a.2 ≤ endBelow s l := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
    simp only [endBelow]
    rcases List.mem_cons.mp ha with rfl | h
    · simp only [hs, ite_true]; omega
    · have := ih h; split <;> omega

theorem endBelow_mem (s : Nat) (l : List (Nat × Nat)) :
    endBelow s l ∈ 0 :: l.map fun a => a.1 + a.2 := by
  induction l with
  | nil => exact List.mem_cons_self
  | cons a as ih =>
    simp only [endBelow, List.map_cons]
    have mono : ∀ x, x ∈ 0 :: as.map (fun a => a.1 + a.2) →
        x ∈ 0 :: (a.1 + a.2) :: as.map (fun a => a.1 + a.2) := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    split
    · rcases Nat.le_total (a.1 + a.2) (endBelow s as) with h | h
      · rw [Nat.max_eq_right h]; exact mono _ ih
      · rw [Nat.max_eq_left h]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact mono _ ih

theorem placement_endBelow {live : List (Nat × Nat)} {size s : Nat}
    (h : Placement live size s) : Placement live size (endBelow s live) := by
  have hle := endBelow_le s live
  refine ⟨by have := h.1; omega, fun a ha => ?_⟩
  rcases h.2 a ha with h' | h'
  · left; omega
  · right; exact le_endBelow s live a ha h'

/-- `placeable` is exact: it holds iff some placement exists. -/
theorem placeable_iff (live : List (Nat × Nat)) (size : Nat) :
    placeable live size = true ↔ ∃ s, Placement live size s := by
  simp only [placeable, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, _, h⟩; exact ⟨s, h⟩
  · rintro ⟨s, h⟩; exact ⟨_, endBelow_mem s live, placement_endBelow h⟩

/-- So `outOfMemory` is reported only when no placement exists. -/
theorem no_placement_of_not_placeable {live : List (Nat × Nat)} {size : Nat}
    (h : placeable live size = false) (s : Nat) : ¬ Placement live size s := fun hs =>
  Bool.false_ne_true (h ▸ (placeable_iff live size).mpr ⟨s, hs⟩)

end Sir.Proofs
