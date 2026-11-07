import Sir.Passes.DeadCode
import ITree.Bisim.Theorems
import Sir.Safety
import Sir.Equivalence.Theorems

namespace Sir.Proofs.DeadCode

open Sir.DeadCode

inductive Reach (n : Nat) (roots : List Nat) (succs : Nat → List Nat) : Nat → Prop
  | root {r} : r ∈ roots → r < n → Reach n roots succs r
  | step {i j} : Reach n roots succs i → j ∈ succs i → j < n → Reach n roots succs j

def visit (s : Array Bool × Array Nat) (j : Nat) : Array Bool × Array Nat :=
  if s.1[j]? = some false then (s.1.setIfInBounds j true, s.2.push j) else s

lemma forIn_visit (l : List Nat) (seen : Array Bool) (work : Array Nat) :
    (forIn (m := Id) l (seen, work) fun j (s : Array Bool × Array Nat) =>
      if s.1[j]? = some false then pure (ForInStep.yield (s.1.setIfInBounds j true, s.2.push j))
      else pure (ForInStep.yield (s.1, s.2))) = l.foldl visit (seen, work) := by
  induction l generalizing seen work with
  | nil => rfl
  | cons j l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    unfold visit
    split <;> exact ih _ _

def Seen (seen : Array Bool) (i : Nat) : Prop := seen[i]? = some true

structure VisitFacts (l : List Nat) (s s' : Array Bool × Array Nat) : Prop where
  size : s'.1.size = s.1.size
  mono : ∀ i, Seen s.1 i → Seen s'.1 i
  cover : ∀ j ∈ l, j < s.1.size → Seen s'.1 j
  keep : ∀ x ∈ s.2, x ∈ s'.2
  new : ∀ i, Seen s'.1 i → Seen s.1 i ∨ (i ∈ s'.2 ∧ i ∈ l)
  pushed : ∀ x ∈ s'.2, x ∈ s.2 ∨ (x ∈ l ∧ Seen s'.1 x)
  count : s'.1.count true + s.2.size = s.1.count true + s'.2.size

lemma seen_set {seen : Array Bool} {j i : Nat} (hj : seen[j]? = some false) :
    Seen (seen.setIfInBounds j true) i ↔ Seen seen i ∨ i = j := by
  unfold Seen
  have hlt : j < seen.size := by
    rcases Nat.lt_or_ge j seen.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hj; cases hj
  rw [Array.getElem?_setIfInBounds]
  by_cases hji : j = i
  · subst hji; simp [hlt]
  · simp [hji, Ne.symm hji]

lemma count_set {seen : Array Bool} {j : Nat} (hj : seen[j]? = some false) :
    (seen.setIfInBounds j true).count true = seen.count true + 1 := by
  have hlt : j < seen.size := by
    rcases Nat.lt_or_ge j seen.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hj; cases hj
  have hf : seen[j] = false := by
    rw [Array.getElem?_eq_getElem hlt] at hj; exact Option.some.inj hj
  simp only [Array.setIfInBounds, hlt, ↓reduceDIte, Array.count_set hlt, hf]
  simp

lemma visitFacts_foldl : ∀ (l : List Nat) (s : Array Bool × Array Nat),
    VisitFacts l s (l.foldl visit s)
  | [], s => ⟨rfl, fun _ h => h, fun _ h _ => (nomatch h), fun _ h => h, fun _ h => Or.inl h,
      fun _ h => Or.inl h, rfl⟩
  | j :: l, s => by
    rw [List.foldl_cons]
    have ih := visitFacts_foldl l (visit s j)
    unfold visit at ih ⊢
    by_cases hj : s.1[j]? = some false
    · simp only [hj, ↓reduceIte] at ih ⊢
      refine ⟨by rw [ih.size, Array.size_setIfInBounds], fun i hi => ih.mono i
          ((seen_set hj).2 (.inl hi)), fun x hx hlt => ?_, fun x hx => ih.keep x
          (Array.mem_push.2 (.inl hx)), fun i hi => ?_, fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ih.mono _ ((seen_set hj).2 (.inr rfl))
        · exact ih.cover x hx (by rw [Array.size_setIfInBounds]; exact hlt)
      · rcases ih.new i hi with h | ⟨hw, hl⟩
        · rcases (seen_set hj).1 h with h | rfl
          · exact .inl h
          · exact .inr ⟨ih.keep _ (Array.mem_push.2 (.inr rfl)), List.mem_cons_self⟩
        · exact .inr ⟨hw, List.mem_cons_of_mem _ hl⟩
      · rcases ih.pushed x hx with h | ⟨hl, hs⟩
        · rcases Array.mem_push.1 h with h | rfl
          · exact .inl h
          · exact .inr ⟨List.mem_cons_self, ih.mono _ ((seen_set hj).2 (.inr rfl))⟩
        · exact .inr ⟨List.mem_cons_of_mem _ hl, hs⟩
      · have := ih.count
        rw [count_set hj, Array.size_push] at this
        omega
    · simp only [hj, ↓reduceIte] at ih ⊢
      exact ⟨ih.size, ih.mono, fun x hx hlt => by
          rcases List.mem_cons.1 hx with rfl | hx
          · refine ih.mono _ ?_
            unfold Seen
            rw [Array.getElem?_eq_getElem hlt] at hj ⊢
            cases h : s.1[x] with
            | true => rfl
            | false => rw [h] at hj; exact absurd rfl hj
          · exact ih.cover x hx hlt, ih.keep, fun i hi => (ih.new i hi).imp id
          fun ⟨h₁, h₂⟩ => ⟨h₁, List.mem_cons_of_mem _ h₂⟩, fun x hx => (ih.pushed x hx).imp id
          fun ⟨h₁, h₂⟩ => ⟨List.mem_cons_of_mem _ h₁, h₂⟩, ih.count⟩

def StepInv {β : Type} (I : Nat → β → Prop) (k : Nat) : ForInStep β → Prop
  | .yield b' => I (k + 1) b'
  | .done b' => ∀ m, k ≤ m → I m b'

lemma forIn_range'_inv {β : Type} (I : Nat → β → Prop) (f : Nat → β → Id (ForInStep β))
    (hf : ∀ k b, I k b → StepInv I k (f k b).run) :
    ∀ (m s : Nat) (b : β), I s b → I (s + m) (forIn (List.range' s m) b f).run
  | 0, s, b, h => h
  | m + 1, s, b, h => by
    rw [List.range'_succ, List.forIn_cons]
    have := hf s b h
    simp only [Id.run_bind]
    unfold StepInv at this
    split at this
    · rename_i b' hb
      rw [hb]
      have := forIn_range'_inv I f hf m (s + 1) b' this
      rw [show s + 1 + m = s + (m + 1) by omega] at this
      exact this
    · rename_i b' hb
      rw [hb]
      exact this _ (by omega)

lemma mem_pop_or {work : Array Nat} {i x : Nat} (hb : work.back? = some i) (hx : x ∈ work) :
    x ∈ work.pop ∨ x = i := by
  rw [Array.back?_eq_getElem?] at hb
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
  have hs : work.size - 1 < work.size := by
    rcases Nat.lt_or_ge (work.size - 1) work.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hb; cases hb
  rw [Array.getElem?_eq_getElem hs] at hb
  by_cases hk' : k = work.size - 1
  · subst hk'; exact .inr (Option.some.inj hb)
  · refine .inl (Array.mem_iff_getElem.2 ⟨k, by rw [Array.size_pop]; omega, ?_⟩)
    rw [Array.getElem_pop]

lemma mem_of_mem_pop {work : Array Nat} {x : Nat} (h : x ∈ work.pop) : x ∈ work := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 h
  rw [Array.getElem_pop]
  exact Array.getElem_mem _

lemma back?_mem {work : Array Nat} {i : Nat} (hb : work.back? = some i) : i ∈ work := by
  rw [Array.back?_eq_getElem?] at hb
  exact Array.mem_of_getElem? hb

lemma back?_size {work : Array Nat} {i : Nat} (hb : work.back? = some i) : 0 < work.size := by
  rcases Nat.eq_zero_or_pos work.size with h | h
  · rw [Array.size_eq_zero_iff] at h; subst h; cases hb
  · exact h

variable {n : Nat} {roots : List Nat} {succs : Nat → List Nat}

structure Inv (n : Nat) (roots : List Nat) (succs : Nat → List Nat) (k : Nat)
    (s : Array Bool × Array Nat) : Prop where
  size : s.1.size = n
  sound : ∀ i, Seen s.1 i → Reach n roots succs i
  work : ∀ x ∈ s.2, Reach n roots succs x
  roots : ∀ r ∈ roots, r < n → Seen s.1 r
  closed : ∀ i, Seen s.1 i → i ∈ s.2 ∨ ∀ j ∈ succs i, j < n → Seen s.1 j
  count : s.2.size = 0 ∨ k + s.2.size ≤ s.1.count true

lemma seen_lt {seen : Array Bool} {i : Nat} (h : Seen seen i) : i < seen.size := by
  rcases Nat.lt_or_ge i seen.size with h' | h'
  · exact h'
  · unfold Seen at h; rw [Array.getElem?_eq_none h'] at h; cases h

lemma inv_init : Inv n roots succs 0 (roots.foldl visit (Array.replicate n false, #[])) := by
  have h := visitFacts_foldl roots (Array.replicate n false, #[])
  have hnot : ∀ i, ¬Seen (Array.replicate n false) i := fun i hi => by
    unfold Seen at hi
    rw [Array.getElem?_replicate] at hi
    split at hi <;> cases hi
  have hsize : (roots.foldl visit (Array.replicate n false, #[])).1.size = n := by
    rw [h.size, Array.size_replicate]
  refine ⟨hsize, fun i hi => ?_, fun x hx => ?_, fun r hr hlt => h.cover r hr (by simpa using hlt),
    fun i hi => ?_, .inr ?_⟩
  · rcases h.new i hi with h' | ⟨_, hl⟩
    · exact (hnot i h').elim
    · exact .root hl (hsize ▸ seen_lt hi)
  · rcases h.pushed x hx with h' | ⟨hl, hs⟩
    · exact absurd h' (by simp)
    · exact .root hl (hsize ▸ seen_lt hs)
  · rcases h.new i hi with h' | ⟨hw, _⟩
    · exact (hnot i h').elim
    · exact .inl hw
  · have := h.count
    have h0 : (Array.replicate n false).count true = 0 := by rw [Array.count_replicate]; simp
    simp [h0] at this
    omega


def mainBody (succs : Nat → List Nat) (_ : Nat) (s : Array Bool × Array Nat) :
    Id (ForInStep (Array Bool × Array Nat)) :=
  match s.2.back? with
  | some i => pure (.yield ((succs i).foldl visit (s.1, s.2.pop)))
  | none => pure (.done s)

lemma reach_eq : reach n roots succs = (forIn (List.range' 0 n)
    (roots.foldl visit (Array.replicate n false, #[])) (mainBody succs)).run.1 := by
  unfold reach
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [forIn_visit]
  simp only [Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero]
  simp only [forIn_visit]
  simp only [Id.run_bind, Id.run_pure]
  refine congrArg (fun (f : Nat → Array Bool × Array Nat → Id (ForInStep (Array Bool × Array Nat))) =>
    (forIn (List.range' 0 n) (roots.foldl visit (Array.replicate n false, #[])) f).run.1)
    (funext fun x => funext fun s => ?_)
  unfold mainBody
  rcases h : s.2.back? with _ | i <;> rfl


lemma inv_step (k : Nat) (s : Array Bool × Array Nat) (h : Inv n roots succs k s) :
    StepInv (Inv n roots succs) k (mainBody succs k s).run := by
  unfold mainBody
  rcases hb : s.2.back? with _ | i
  · intro m _
    exact ⟨h.size, h.sound, h.work, h.roots, h.closed,
      .inl (by rw [Array.size_eq_zero_iff]; exact Array.back?_eq_none_iff.1 hb)⟩
  · show Inv n roots succs (k + 1) ((succs i).foldl visit (s.1, s.2.pop))
    have v := visitFacts_foldl (succs i) (s.1, s.2.pop)
    have hi := back?_mem hb
    have hri := h.work i hi
    have hsz := back?_size hb
    refine ⟨v.size.trans h.size, fun j hj => ?_, fun x hx => ?_, fun r hr hlt => v.mono r (h.roots r hr hlt),
      fun j hj => ?_, .inr ?_⟩
    · rcases v.new j hj with hj' | ⟨_, hl⟩
      · exact h.sound j hj'
      · exact .step hri hl (v.size.trans h.size ▸ seen_lt hj)
    · rcases v.pushed x hx with hx' | ⟨hl, hs⟩
      · exact h.work x (mem_of_mem_pop hx')
      · exact .step hri hl (v.size.trans h.size ▸ seen_lt hs)
    · rcases v.new j hj with hj' | ⟨hw, _⟩
      · rcases h.closed j hj' with hw | hc
        · rcases mem_pop_or hb hw with hw | rfl
          · exact .inl (v.keep _ hw)
          · exact .inr fun t ht hlt => v.cover t ht (h.size ▸ hlt)
        · exact .inr fun t ht hlt => v.mono t (hc t ht hlt)
      · exact .inl hw
    · have hc := v.count
      dsimp only at hc
      rw [Array.size_pop] at hc
      rcases h.count with h0 | h1
      · omega
      · omega

theorem reach_size : (reach n roots succs).size = n := by
  rw [reach_eq]
  exact (forIn_range'_inv (Inv n roots succs) (mainBody succs) inv_step n 0 _ inv_init).size

theorem reach_iff (i : Nat) : (reach n roots succs)[i]? = some true ↔ Reach n roots succs i := by
  rw [reach_eq]
  have h := forIn_range'_inv (Inv n roots succs) (mainBody succs) inv_step n 0 _ inv_init
  rw [Nat.zero_add] at h
  generalize (forIn (List.range' 0 n) (roots.foldl visit (Array.replicate n false, #[]))
    (mainBody succs)).run = s at h
  have hw : s.2.size = 0 := by
    rcases h.count with h0 | h1
    · exact h0
    · have := Array.count_le_size (a := true) (xs := s.1); rw [h.size] at this; omega
  have hclosed : ∀ i, Seen s.1 i → ∀ j ∈ succs i, j < n → Seen s.1 j := fun i hi => by
    rcases h.closed i hi with hm | hc
    · rw [Array.size_eq_zero_iff] at hw; rw [hw] at hm; simp at hm
    · exact hc
  refine ⟨h.sound i, fun hr => ?_⟩
  induction hr with
  | root hr hlt => exact h.roots _ hr hlt
  | step _ hj hlt ih => exact hclosed _ ih _ hj hlt


section Lists

variable {α β : Type}

def renumberList : List Bool → Nat → List (Option Nat)
  | [], _ => []
  | true :: ls, n => some n :: renumberList ls (n + 1)
  | false :: ls, n => none :: renumberList ls n

def keepList (g : α → β) : List α → List Bool → List β
  | x :: xs, true :: ls => g x :: keepList g xs ls
  | _ :: xs, false :: ls => keepList g xs ls
  | _, _ => []

lemma renumberList_length : ∀ (ls : List Bool) (n : Nat), (renumberList ls n).length = ls.length
  | [], _ => rfl
  | true :: ls, n => by simp [renumberList, renumberList_length ls]
  | false :: ls, n => by simp [renumberList, renumberList_length ls]

lemma renumberList_some : ∀ (ls : List Bool) (n i j : Nat),
    (renumberList ls n)[i]? = some (some j) → ls[i]? = some true ∧ n ≤ j
  | [], _, _, _, h => by simp [renumberList] at h
  | true :: ls, n, 0, j, h => by simp [renumberList] at h; simp [h]
  | false :: ls, n, 0, j, h => by simp [renumberList] at h
  | true :: ls, n, i + 1, j, h => by
    simp only [renumberList, List.getElem?_cons_succ] at h
    have := renumberList_some ls (n + 1) i j h
    exact ⟨by simpa using this.1, by omega⟩
  | false :: ls, n, i + 1, j, h => by
    simp only [renumberList, List.getElem?_cons_succ] at h
    have := renumberList_some ls n i j h
    exact ⟨by simpa using this.1, this.2⟩

lemma renumberList_inj : ∀ (ls : List Bool) (n i i' j : Nat),
    (renumberList ls n)[i]? = some (some j) → (renumberList ls n)[i']? = some (some j) → i = i'
  | [], _, _, _, _, h, _ => by simp [renumberList] at h
  | true :: ls, n, 0, 0, j, _, _ => rfl
  | true :: ls, n, 0, i' + 1, j, h, h' => by
    simp only [renumberList, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h h'
    have := (renumberList_some ls (n + 1) i' j h').2
    omega
  | true :: ls, n, i + 1, 0, j, h, h' => by
    simp only [renumberList, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h h'
    have := (renumberList_some ls (n + 1) i j h).2
    omega
  | true :: ls, n, i + 1, i' + 1, j, h, h' => by
    simp only [renumberList, List.getElem?_cons_succ] at h h'
    rw [renumberList_inj ls (n + 1) i i' j h h']
  | false :: ls, n, 0, _, j, h, _ => by simp [renumberList] at h
  | false :: ls, n, _ + 1, 0, j, _, h' => by simp [renumberList] at h'
  | false :: ls, n, i + 1, i' + 1, j, h, h' => by
    simp only [renumberList, List.getElem?_cons_succ] at h h'
    rw [renumberList_inj ls n i i' j h h']

lemma keepList_of_live (g : α → β) : ∀ (xs : List α) (ls : List Bool) (n i : Nat) (x : α),
    xs[i]? = some x → ls[i]? = some true →
      ∃ k, (renumberList ls n)[i]? = some (some (n + k)) ∧ (keepList g xs ls)[k]? = some (g x)
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | y :: xs, true :: ls, n, 0, x, h, _ => ⟨0, by simp [renumberList], by simp_all [keepList]⟩
  | y :: xs, false :: ls, n, 0, x, _, h => by simp at h
  | y :: xs, true :: ls, n, i + 1, x, h, h' => by
    obtain ⟨k, hk, hk'⟩ := keepList_of_live g xs ls (n + 1) i x (by simpa using h) (by simpa using h')
    refine ⟨k + 1, ?_, ?_⟩
    · simp only [renumberList, List.getElem?_cons_succ, hk]; congr 2; omega
    · simpa [keepList] using hk'
  | y :: xs, false :: ls, n, i + 1, x, h, h' => by
    obtain ⟨k, hk, hk'⟩ := keepList_of_live g xs ls n i x (by simpa using h) (by simpa using h')
    exact ⟨k, by simpa [renumberList] using hk, by simpa [keepList] using hk'⟩

lemma keepList_mem (g : α → β) : ∀ (xs : List α) (ls : List Bool) (n k : Nat) (y : β),
    (keepList g xs ls)[k]? = some y →
      ∃ (i : Nat) (x : α), xs[i]? = some x ∧ ls[i]? = some true ∧
        (renumberList ls n)[i]? = some (some (n + k)) ∧ y = g x
  | [], _, _, _, _, h => by simp [keepList] at h
  | _ :: _, [], _, _, _, h => by simp [keepList] at h
  | x :: xs, true :: ls, n, 0, y, h => ⟨0, x, rfl, rfl, by simp [renumberList], by
      simp [keepList] at h; exact h.symm⟩
  | x :: xs, true :: ls, n, k + 1, y, h => by
    obtain ⟨i, x', h₁, h₂, h₃, h₄⟩ := keepList_mem g xs ls (n + 1) k y (by simpa [keepList] using h)
    refine ⟨i + 1, x', by simpa using h₁, by simpa using h₂, ?_, h₄⟩
    simp only [renumberList, List.getElem?_cons_succ, h₃]; congr 2; omega
  | x :: xs, false :: ls, n, k, y, h => by
    obtain ⟨i, x', h₁, h₂, h₃, h₄⟩ := keepList_mem g xs ls n k y (by simpa [keepList] using h)
    exact ⟨i + 1, x', by simpa using h₁, by simpa using h₂, by simpa [renumberList] using h₃, h₄⟩

end Lists


lemma forIn_renumber : ∀ (ls : List Bool) (ids : Array (Option Nat)) (n : Nat),
    (forIn (m := Id) ls (ids, n) fun l (s : Array (Option Nat) × Nat) =>
      if l = true then pure (ForInStep.yield (s.1.push (some s.2), s.2 + 1))
      else pure (ForInStep.yield (s.1.push none, s.2))).run.1.toList =
      ids.toList ++ renumberList ls n
  | [], ids, n => by simp [renumberList]
  | true :: ls, ids, n => by
    rw [List.forIn_cons]
    simp only [↓reduceIte, Id.run_bind, Id.run_pure]
    rw [forIn_renumber ls]
    simp [renumberList]
  | false :: ls, ids, n => by
    rw [List.forIn_cons]
    simp only [Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure]
    rw [forIn_renumber ls]
    simp [renumberList]

lemma renumber_toList (L : Array Bool) : (renumber L).toList = renumberList L.toList 0 := by
  unfold renumber
  simp only [← Array.forIn_toList, Id.run_bind, Id.run_pure]
  rw [forIn_renumber]
  rfl

lemma renumber_getElem? (L : Array Bool) (i : Nat) :
    (renumber L)[i]? = (renumberList L.toList 0)[i]? := by
  rw [← renumber_toList, Array.getElem?_toList]


lemma forIn_eq_foldl_of {γ δ : Type} (xs : Array γ) (b : δ) (f : γ → δ → Id (ForInStep δ))
    (F : δ → γ → δ) (h : ∀ a s, f a s = pure (.yield (F s a))) :
    forIn xs b f = pure (xs.foldl F b) := by
  rw [show f = fun a s => pure (.yield (F s a)) from funext fun a => funext fun s => h a s]
  exact Array.forIn_pure_yield_eq_foldl _ _

def keepF {α β : Type} (L : Array Bool) (g : α → β) (s : Array β) (x : α × Nat) : Array β :=
  if L[x.2]? = some true then s.push (g x.1) else s

lemma foldl_keepF {α β : Type} (L : Array Bool) (g : α → β) : ∀ (xs : List α) (k : Nat) (acc : Array β),
    L.size = k + xs.length →
      ((xs.zipIdx k).foldl (keepF L g) acc).toList = acc.toList ++ keepList g xs (L.toList.drop k)
  | [], k, acc, _ => by simp [keepList]
  | x :: xs, k, acc, h => by
    have hk : k < L.size := by simp at h; omega
    have hd : L.toList.drop k = L[k] :: L.toList.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hk)]; simp
    rw [List.zipIdx_cons, List.foldl_cons, foldl_keepF L g xs (k + 1) _ (by simp at h; omega), hd]
    unfold keepF
    simp only [Array.getElem?_eq_getElem hk]
    cases L[k] <;> simp [keepList]

lemma keep_toList {α β : Type} (L : Array Bool) (g : α → β) (xs : Array α) (h : L.size = xs.size) :
    (xs.zipIdx.foldl (keepF L g) #[]).toList = keepList g xs.toList L.toList := by
  rw [← Array.foldl_toList, Array.toList_zipIdx, foldl_keepF L g xs.toList 0 #[] (by simpa using h)]
  simp

def pushCallee (s : Array Nat) (op : Operation VarId) : Array Nat :=
  match op.callee? with
  | some g => s.push g.id
  | none => s

def pushBlockCallees (s : Array Nat) (b : Block) : Array Nat :=
  match b.control.callee? with
  | some g => (b.ops.foldl pushCallee s).push g.id
  | none => b.ops.foldl pushCallee s

lemma mem_foldl_pushCallee : ∀ (ops : List (Operation VarId)) (s : Array Nat) (x : Nat),
    x ∈ ops.foldl pushCallee s ↔ x ∈ s ∨ ∃ op ∈ ops, op.callee? = some ⟨x⟩
  | [], s, x => by simp
  | op :: ops, s, x => by
    rw [List.foldl_cons, mem_foldl_pushCallee ops]
    unfold pushCallee
    rcases h : op.callee? with _ | g
    · simp [h]
    · simp only [Array.mem_push, List.mem_cons, exists_eq_or_imp, h, Option.some.injEq]
      constructor
      · rintro ((h | rfl) | h)
        · exact .inl h
        · exact .inr (.inl rfl)
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · subst h; exact .inl (.inr rfl)
        · exact .inr h

lemma mem_pushBlockCallees (s : Array Nat) (b : Block) (x : Nat) :
    x ∈ pushBlockCallees s b ↔ x ∈ s ∨ b.Calls ⟨x⟩ := by
  unfold pushBlockCallees Block.Calls
  rcases h : b.control.callee? with _ | g
  · simp only [← Array.foldl_toList, mem_foldl_pushCallee, Array.mem_toList_iff]
    simp
  · simp only [Array.mem_push, ← Array.foldl_toList, mem_foldl_pushCallee, Array.mem_toList_iff,
      Option.some.injEq]
    constructor
    · rintro ((h | h) | rfl)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr rfl)
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · subst h; exact .inr rfl

def calleesF (L : Array Bool) (s : Array Nat) (x : Block × Nat) : Array Nat :=
  if L[x.2]? = some true then pushBlockCallees s x.1 else s

lemma mem_foldl_calleesF (L : Array Bool) : ∀ (l : List (Block × Nat)) (s : Array Nat) (x : Nat),
    x ∈ l.foldl (calleesF L) s ↔ x ∈ s ∨ ∃ b i, (b, i) ∈ l ∧ L[i]? = some true ∧ b.Calls ⟨x⟩
  | [], s, x => by simp
  | (b, i) :: l, s, x => by
    rw [List.foldl_cons, mem_foldl_calleesF L l]
    unfold calleesF
    by_cases hi : L[i]? = some true
    · simp only [hi, ↓reduceIte, mem_pushBlockCallees, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro ((h | h) | ⟨b', i', h₁, h₂, h₃⟩)
        · exact .inl h
        · exact .inr ⟨b, i, .inl ⟨rfl, rfl⟩, hi, h⟩
        · exact .inr ⟨b', i', .inr h₁, h₂, h₃⟩
      · rintro (h | ⟨b', i', (⟨rfl, rfl⟩ | h₁), h₂, h₃⟩)
        · exact .inl (.inl h)
        · exact .inl (.inr h₃)
        · exact .inr ⟨b', i', h₁, h₂, h₃⟩
    · simp only [hi, ↓reduceIte, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (h | ⟨b', i', h₁, h₂, h₃⟩)
        · exact .inl h
        · exact .inr ⟨b', i', .inr h₁, h₂, h₃⟩
      · rintro (h | ⟨b', i', (⟨rfl, rfl⟩ | h₁), h₂, h₃⟩)
        · exact .inl h
        · exact absurd h₂ hi
        · exact .inr ⟨b', i', h₁, h₂, h₃⟩

lemma liveCallees_eq (fn : Function) :
    fn.liveCallees = (fn.blocks.zipIdx.foldl (calleesF fn.liveBlocks) #[]).toList := by
  unfold Function.liveCallees
  simp only [Id.run_bind, Id.run_pure]
  rw [forIn_eq_foldl_of _ _ _ (calleesF fn.liveBlocks) fun ⟨b, i⟩ s => by
    unfold calleesF pushBlockCallees
    simp only
    split
    · rw [forIn_eq_foldl_of _ _ _ pushCallee fun op s => by
        unfold pushCallee; generalize op.callee? = c; cases c <;> rfl]
      generalize b.control.callee? = c; cases c <;> rfl
    · rfl]
  rfl

lemma mem_liveCallees (fn : Function) (g : Nat) :
    g ∈ fn.liveCallees ↔ ∃ (b : BlockId) (blk : Block), fn.liveBlocks[b.id]? = some true ∧ fn[b]? = some blk ∧ blk.Calls ⟨g⟩ := by
  rw [liveCallees_eq, Array.mem_toList_iff, ← Array.foldl_toList, mem_foldl_calleesF, Array.toList_zipIdx]
  simp only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList]
  constructor
  · rintro (h | ⟨b, i, h₁, h₂, h₃⟩)
    · simp at h
    · exact ⟨⟨i⟩, b, h₂, h₁, h₃⟩
  · rintro ⟨b, blk, h₁, h₂, h₃⟩
    exact .inr ⟨blk, b.id, h₂, h₁, h₃⟩


lemma getElem?_lt {γ : Type} {xs : Array γ} {i : Nat} {x : γ} (h : xs[i]? = some x) : i < xs.size := by
  rcases Nat.lt_or_ge i xs.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; cases h

lemma liveBlocks_size (fn : Function) : fn.liveBlocks.size = fn.blocks.size := reach_size

lemma liveBlocks_iff (fn : Function) (hwf : fn.WF) (b : BlockId) :
    fn.liveBlocks[b.id]? = some true ↔ ∃ prev, fn.PathTo prev b := by
  unfold Function.liveBlocks
  rw [reach_iff]
  constructor
  · intro h
    obtain ⟨i⟩ := b
    dsimp only at h ⊢
    induction h with
    | root hr _ =>
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨[], .entry⟩
    | @step i j _ hj _ ih =>
      obtain ⟨prev, hp⟩ := ih
      revert hj
      rcases hblk : fn.blocks[i]? with _ | blk
      · simp
      · intro hj
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hj
        exact ⟨prev ++ [blk], .step hp hblk ht⟩
  · rintro ⟨prev, hp⟩
    induction hp with
    | entry => exact .root (List.mem_singleton_self _) hwf.entry_valid
    | @step prev b blk t _ hblk ht ih =>
      obtain ⟨tb, htb, _⟩ := hwf.validTargets blk (Array.mem_of_getElem? hblk) t ht
      refine .step ih ?_ (getElem?_lt htb)
      show t.id ∈ (match fn.blocks[b.id]? with
        | some (b' : Block) => b'.control.targets.map (fun t : BlockId => t.id) | none => [])
      rw [show fn.blocks[b.id]? = some blk from hblk]
      exact List.mem_map_of_mem ht

lemma calls_callee {p : Program} (hwf : p.WF) {fn : Function} (hfn : fn ∈ p.functions)
    {blk : Block} (hb : blk ∈ fn.blocks) {g : FunctionId} (hc : blk.Calls g) :
    ∃ fn', p[g]? = some fn' := by
  have hv := hwf.validCalls fn hfn blk hb
  rcases hc with ⟨op, hop, hg⟩ | hg
  · have := hv.1 op hop
    cases op with
    | icall g' ins outs =>
      cases hg
      obtain ⟨fn', h, _⟩ := this
      exact ⟨fn', h⟩
    | _ => cases hg
  · have := hv.2
    revert this hg
    cases blk.control with
    | icallNever g' ins =>
      intro hg this
      cases hg
      obtain ⟨fn', h, _⟩ := this
      exact ⟨fn', h⟩
    | _ => intro hg; cases hg

lemma callEdge_iff (p : Program) (hwf : p.WF) (f g : FunctionId) :
    p.CallEdge f g ↔ ∃ fn, p[f]? = some fn ∧ g.id ∈ fn.liveCallees := by
  constructor
  · rintro ⟨fn, hfn, prev, b, blk, hp, hblk, hc⟩
    have hfwf := hwf.functions fn (Array.mem_of_getElem? hfn)
    exact ⟨fn, hfn, (mem_liveCallees fn g.id).2
      ⟨b, blk, (liveBlocks_iff fn hfwf b).2 ⟨prev, hp⟩, hblk, hc⟩⟩
  · rintro ⟨fn, hfn, hg⟩
    have hfwf := hwf.functions fn (Array.mem_of_getElem? hfn)
    obtain ⟨b, blk, hl, hblk, hc⟩ := (mem_liveCallees fn g.id).1 hg
    obtain ⟨prev, hp⟩ := (liveBlocks_iff fn hfwf b).1 hl
    exact ⟨fn, hfn, prev, b, blk, hp, hblk, hc⟩

lemma liveFunctions_size (p : Program) : p.liveFunctions.size = p.functions.size := reach_size

lemma liveFunctions_iff (p : Program) (hwf : p.WF) (f : FunctionId) :
    p.liveFunctions[f.id]? = some true ↔ p.Reachable p.init f ∨ p.Reachable p.main f := by
  unfold Program.liveFunctions
  rw [reach_iff]
  constructor
  · intro h
    obtain ⟨i⟩ := f
    dsimp only at h ⊢
    induction h with
    | root hr _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl .root
      · exact .inr .root
    | @step i j _ hj _ ih =>
      revert hj
      rcases hfn : p.functions[i]? with _ | fn
      · simp
      · intro hj
        have he : p.CallEdge ⟨i⟩ ⟨j⟩ := (callEdge_iff p hwf ⟨i⟩ ⟨j⟩).2 ⟨fn, hfn, hj⟩
        exact ih.imp (fun h => .call h he) (fun h => .call h he)
  · have hroot : ∀ r, r.id ∈ [p.init.id, p.main.id] → (∃ fn, p[r]? = some fn) → ∀ f,
        p.Reachable r f → Reach p.functions.size [p.init.id, p.main.id] (fun i =>
          match p.functions[i]? with | some fn => fn.liveCallees | none => []) f.id := by
      intro r hr ⟨fn, hfn⟩ f h
      induction h with
      | root => exact .root hr (getElem?_lt hfn)
      | @call f g _ he ih =>
        obtain ⟨fn', hfn', hg⟩ := (callEdge_iff p hwf f g).1 he
        obtain ⟨fnE, hfnE, _, b, blk, _, hblk, hc⟩ := he
        obtain ⟨_, hg'⟩ := calls_callee hwf (Array.mem_of_getElem? hfnE)
          (Array.mem_of_getElem? (show fnE.blocks[b.id]? = some blk from hblk)) hc
        refine .step ih ?_ (getElem?_lt hg')
        show g.id ∈ (match p.functions[f.id]? with | some fn => fn.liveCallees | none => [])
        rw [show p.functions[f.id]? = some fn' from hfn']
        exact hg
    obtain ⟨fi, hfi, _⟩ := hwf.initEntry
    obtain ⟨fm, hfm, _⟩ := hwf.mainEntry
    rintro (h | h)
    · exact hroot _ (by simp) ⟨fi, hfi⟩ f h
    · exact hroot _ (by simp) ⟨fm, hfm⟩ f h


section Keep

variable {α β : Type}

lemma rename_of_some {ids : Array (Option Nat)} {i k : Nat} (h : ids[i]? = some (some k)) :
    rename ids i = k := by
  unfold rename; rw [h]

lemma keep_live (L : Array Bool) (xs : Array α) (g : α → β)
    (out : Array β) (hout : out.toList = keepList g xs.toList L.toList) (i : Nat) (x : α)
    (hx : xs[i]? = some x) (hl : L[i]? = some true) :
    (renumber L)[i]? = some (some (rename (renumber L) i)) ∧ out[rename (renumber L) i]? = some (g x) := by
  obtain ⟨k, hk, hk'⟩ := keepList_of_live g xs.toList L.toList 0 i x (by simpa using hx)
    (by simpa using hl)
  rw [Nat.zero_add, ← renumber_getElem?] at hk
  rw [rename_of_some hk]
  refine ⟨hk, ?_⟩
  rw [← Array.getElem?_toList, hout]
  exact hk'

lemma keep_inv (L : Array Bool) (xs : Array α) (g : α → β) (out : Array β)
    (hout : out.toList = keepList g xs.toList L.toList) (k : Nat) (y : β) (hy : out[k]? = some y) :
    ∃ i x, xs[i]? = some x ∧ L[i]? = some true ∧ rename (renumber L) i = k ∧ y = g x := by
  rw [← Array.getElem?_toList, hout] at hy
  obtain ⟨i, x, h₁, h₂, h₃, h₄⟩ := keepList_mem g xs.toList L.toList 0 k y hy
  rw [Nat.zero_add, ← renumber_getElem?] at h₃
  exact ⟨i, x, by simpa using h₁, by simpa using h₂, rename_of_some h₃, h₄⟩

lemma keep_inj (L : Array Bool) (xs : Array α) (hsz : L.size = xs.size) (i i' : Nat)
    (hl : L[i]? = some true) (hl' : L[i']? = some true)
    (he : rename (renumber L) i = rename (renumber L) i') : i = i' := by
  have hx : ∀ j, L[j]? = some true → ∃ x, xs[j]? = some x := fun j hj =>
    ⟨xs[j]'(hsz ▸ getElem?_lt hj), Array.getElem?_eq_getElem _⟩
  obtain ⟨x, hx₁⟩ := hx i hl
  obtain ⟨x', hx₂⟩ := hx i' hl'
  have h₁ := (keep_live L xs id (keepList id xs.toList L.toList).toArray (by simp) i x hx₁ hl).1
  have h₂ := (keep_live L xs id (keepList id xs.toList L.toList).toArray (by simp) i' x' hx₂ hl').1
  rw [renumber_getElem?] at h₁ h₂
  rw [he] at h₁
  exact renumberList_inj _ 0 i i' _ h₁ h₂

end Keep

section Sweep

abbrev blockIds (fn : Function) : Array (Option Nat) := renumber fn.liveBlocks

def blockMapOf (fn : Function) (b : BlockId) : BlockId := ⟨rename (blockIds fn) b.id⟩

def fnMapOf (p : Program) (f : FunctionId) : FunctionId := ⟨rename (renumber p.liveFunctions) f.id⟩

lemma sweep_blocks (φ : FunctionId → FunctionId) (fn : Function) :
    (fn.sweep φ).blocks.toList = keepList (Block.rename (blockMapOf fn) φ) fn.blocks.toList
      fn.liveBlocks.toList := by
  unfold Function.sweep
  simp only [Id.run_bind, Id.run_pure]
  rw [forIn_eq_foldl_of _ _ _ (keepF fn.liveBlocks (Block.rename (blockMapOf fn) φ)) fun ⟨b, i⟩ s => by
    unfold keepF; split <;> rfl]
  exact keep_toList _ _ _ (liveBlocks_size fn)

lemma sweep_entry (φ : FunctionId → FunctionId) (fn : Function) :
    (fn.sweep φ).entry = blockMapOf fn fn.entry := rfl

lemma sweep_returns (φ : FunctionId → FunctionId) (fn : Function) :
    (fn.sweep φ).returns = fn.returns := rfl

lemma removeDeadCode_functions (p : Program) :
    p.removeDeadCode.functions.toList = keepList (Function.sweep (fnMapOf p)) p.functions.toList
      p.liveFunctions.toList := by
  unfold Program.removeDeadCode
  simp only [Id.run_bind, Id.run_pure]
  rw [forIn_eq_foldl_of _ _ _ (keepF p.liveFunctions (Function.sweep (fnMapOf p))) fun ⟨b, i⟩ s => by
    unfold keepF; split <;> rfl]
  exact keep_toList _ _ _ (liveFunctions_size p)

lemma removeDeadCode_init (p : Program) : p.removeDeadCode.init = fnMapOf p p.init := rfl
lemma removeDeadCode_main (p : Program) : p.removeDeadCode.main = fnMapOf p p.main := rfl

abbrev LiveFn (p : Program) (f : FunctionId) : Prop := p.liveFunctions[f.id]? = some true
abbrev LiveBlock (fn : Function) (b : BlockId) : Prop := fn.liveBlocks[b.id]? = some true

lemma sweep_live {φ : FunctionId → FunctionId} {fn : Function} {b : BlockId} {blk : Block}
    (hl : LiveBlock fn b) (hb : fn[b]? = some blk) :
    (fn.sweep φ)[blockMapOf fn b]? = some (blk.rename (blockMapOf fn) φ) :=
  (keep_live _ _ _ _ (sweep_blocks φ fn) b.id blk hb hl).2

lemma sweep_inv {φ : FunctionId → FunctionId} {fn : Function} {b' : BlockId} {blk' : Block}
    (h : (fn.sweep φ)[b']? = some blk') :
    ∃ b blk, LiveBlock fn b ∧ fn[b]? = some blk ∧ blockMapOf fn b = b' ∧
      blk' = blk.rename (blockMapOf fn) φ := by
  obtain ⟨i, x, h₁, h₂, h₃, h₄⟩ := keep_inv _ _ _ _ (sweep_blocks φ fn) b'.id blk' h
  exact ⟨⟨i⟩, x, h₂, h₁, by rw [blockMapOf]; simp only [h₃], h₄⟩

lemma blockMapOf_inj {fn : Function} {b c : BlockId} (hb : LiveBlock fn b) (hc : LiveBlock fn c)
    (h : blockMapOf fn b = blockMapOf fn c) : b = c := by
  have := keep_inj _ _ (liveBlocks_size fn) b.id c.id hb hc (congrArg BlockId.id h)
  cases b; cases c; simp_all

lemma removeDeadCode_live {p : Program} {f : FunctionId} {fn : Function} (hl : LiveFn p f)
    (hf : p[f]? = some fn) : p.removeDeadCode[fnMapOf p f]? = some (fn.sweep (fnMapOf p)) :=
  (keep_live _ _ _ _ (removeDeadCode_functions p) f.id fn hf hl).2

lemma removeDeadCode_inv {p : Program} {f' : FunctionId} {fn' : Function}
    (h : p.removeDeadCode[f']? = some fn') :
    ∃ f fn, LiveFn p f ∧ p[f]? = some fn ∧ fnMapOf p f = f' ∧ fn' = fn.sweep (fnMapOf p) := by
  obtain ⟨i, x, h₁, h₂, h₃, h₄⟩ := keep_inv _ _ _ _ (removeDeadCode_functions p) f'.id fn' h
  exact ⟨⟨i⟩, x, h₂, h₁, by rw [fnMapOf]; simp only [h₃], h₄⟩

lemma fnMapOf_inj {p : Program} {f g : FunctionId} (hf : LiveFn p f) (hg : LiveFn p g)
    (h : fnMapOf p f = fnMapOf p g) : f = g := by
  have := keep_inj _ _ (liveFunctions_size p) f.id g.id hf hg (congrArg FunctionId.id h)
  cases f; cases g; simp_all

end Sweep

open Host CoFree

section Live

lemma keepList_length_le {α β : Type} (g : α → β) :
    ∀ (xs : List α) (ls : List Bool), (keepList g xs ls).length ≤ ls.length
  | _ :: xs, true :: ls => by simp only [keepList, List.length_cons]; have := keepList_length_le g xs ls; omega
  | _ :: xs, false :: ls => by simp only [keepList, List.length_cons]; have := keepList_length_le g xs ls; omega
  | [], _ => by simp [keepList]
  | _ :: _, [] => by simp [keepList]

lemma renumber_size (L : Array Bool) : (renumber L).size = L.size := by
  rw [← Array.length_toList, renumber_toList, renumberList_length, Array.length_toList]

lemma rename_of_none {ids : Array (Option Nat)} {i : Nat} (h : ids[i]? = none) :
    rename ids i = ids.size := by
  unfold rename; rw [h]

lemma sweep_size_le (φ : FunctionId → FunctionId) (fn : Function) :
    (fn.sweep φ).blocks.size ≤ fn.blocks.size := by
  rw [← Array.length_toList, sweep_blocks]
  exact Nat.le_trans (keepList_length_le _ _ _) (by simp [liveBlocks_size])

lemma removeDeadCode_size_le (p : Program) : p.removeDeadCode.functions.size ≤ p.functions.size := by
  rw [← Array.length_toList, removeDeadCode_functions]
  exact Nat.le_trans (keepList_length_le _ _ _) (by simp [liveFunctions_size])

lemma sweep_none {φ : FunctionId → FunctionId} {fn : Function} {b : BlockId} (h : fn[b]? = none) :
    (fn.sweep φ)[blockMapOf fn b]? = none := by
  have hb : fn.blocks.size ≤ b.id := Array.getElem?_eq_none_iff.1 h
  have hr : rename (blockIds fn) b.id = fn.blocks.size := by
    rw [rename_of_none (Array.getElem?_eq_none_iff.2 (by rw [renumber_size, liveBlocks_size]; exact hb)),
      renumber_size, liveBlocks_size]
  show (fn.sweep φ).blocks[rename (blockIds fn) b.id]? = none
  rw [hr]
  exact Array.getElem?_eq_none_iff.2 (sweep_size_le φ fn)

lemma removeDeadCode_none {p : Program} {f : FunctionId} (h : p[f]? = none) :
    p.removeDeadCode[fnMapOf p f]? = none := by
  have hf : p.functions.size ≤ f.id := Array.getElem?_eq_none_iff.1 h
  have hr : rename (renumber p.liveFunctions) f.id = p.functions.size := by
    rw [rename_of_none (Array.getElem?_eq_none_iff.2 (by rw [renumber_size, liveFunctions_size]; exact hf)),
      renumber_size, liveFunctions_size]
  show p.removeDeadCode.functions[rename (renumber p.liveFunctions) f.id]? = none
  rw [hr]
  exact Array.getElem?_eq_none_iff.2 (removeDeadCode_size_le p)

lemma reach_lt {n : Nat} {roots : List Nat} {succs : Nat → List Nat} {i : Nat}
    (h : Reach n roots succs i) : i < n := by
  cases h <;> assumption

lemma liveBlock_some {fn : Function} {b : BlockId} (hl : LiveBlock fn b) : ∃ blk, fn[b]? = some blk := by
  unfold LiveBlock Function.liveBlocks at hl
  rw [reach_iff] at hl
  exact ⟨_, Array.getElem?_eq_getElem (reach_lt hl)⟩

lemma liveFn_some {p : Program} {f : FunctionId} (hl : LiveFn p f) : ∃ fn, p[f]? = some fn := by
  unfold LiveFn Program.liveFunctions at hl
  rw [reach_iff] at hl
  exact ⟨_, Array.getElem?_eq_getElem (reach_lt hl)⟩

lemma liveBlock_entry (fn : Function) : LiveBlock fn fn.entry ∨ fn[fn.entry]? = none := by
  by_cases h : fn.entry.id < fn.blocks.size
  · left
    unfold LiveBlock Function.liveBlocks
    rw [reach_iff]
    exact .root (List.mem_singleton_self _) h
  · exact .inr (Array.getElem?_eq_none_iff.2 (by omega))

lemma liveBlock_succ {fn : Function} {b t : BlockId} {blk : Block} (hl : LiveBlock fn b)
    (hb : fn[b]? = some blk) (ht : t ∈ blk.control.targets) : LiveBlock fn t ∨ fn[t]? = none := by
  by_cases h : t.id < fn.blocks.size
  · left
    unfold LiveBlock Function.liveBlocks at hl ⊢
    rw [reach_iff] at hl ⊢
    refine .step hl ?_ h
    show t.id ∈ (match fn.blocks[b.id]? with
      | some (b' : Block) => b'.control.targets.map (fun t : BlockId => t.id) | none => [])
    rw [show fn.blocks[b.id]? = some blk from hb]
    exact List.mem_map_of_mem ht
  · exact .inr (Array.getElem?_eq_none_iff.2 (by omega))

lemma liveFn_root {p : Program} {r : FunctionId} (hr : r.id ∈ [p.init.id, p.main.id]) :
    LiveFn p r ∨ p[r]? = none := by
  by_cases h : r.id < p.functions.size
  · left
    unfold LiveFn Program.liveFunctions
    rw [reach_iff]
    exact .root hr h
  · exact .inr (Array.getElem?_eq_none_iff.2 (by omega))

lemma liveFn_succ {p : Program} {f g : FunctionId} {fn : Function} {b : BlockId} {blk : Block}
    (hl : LiveFn p f) (hf : p[f]? = some fn) (hlb : LiveBlock fn b) (hb : fn[b]? = some blk)
    (hc : blk.Calls g) : LiveFn p g ∨ p[g]? = none := by
  by_cases h : g.id < p.functions.size
  · left
    unfold LiveFn Program.liveFunctions at hl ⊢
    rw [reach_iff] at hl ⊢
    refine .step hl ?_ h
    show g.id ∈ (match p.functions[f.id]? with | some fn => fn.liveCallees | none => [])
    rw [show p.functions[f.id]? = some fn from hf]
    exact (mem_liveCallees fn g.id).2 ⟨b, blk, hlb, hb, hc⟩
  · exact .inr (Array.getElem?_eq_none_iff.2 (by omega))

end Live

section Leaves

abbrev RecE := Effect.Rec CallI CallO EvalE

abbrev CallRel (RI : CallI → CallI → Prop) : OpRel RecE := OpRel.calls RI (OpRel.eq EvalE)

variable {RI : CallI → CallI → Prop}

lemma bisim_lift {α β : Type} {Ret : α → β → Prop} {m₁ : SirM α} {m₂ : SirM β}
    (h : Bisim (OpRel.eq EvalE) Ret m₁ m₂) :
    Bisim (CallRel RI) Ret (m₁.mapOps ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none α)
      (m₂.mapOps ⟨Sum.inr, fun _ r => r⟩ .id) :=
  Bisim.mapOps (fun _ _ h => h) (fun _ _ _ _ _ h => h) h

lemma bisim_liftHost {α β : Type} {Ret : α → β → Prop} {m₁ : HostM α} {m₂ : HostM β}
    (h : Bisim (OpRel.eq HostE) Ret m₁ m₂) :
    Bisim (OpRel.eq EvalE) Ret (m₁.mapOps ⟨Sum.inl, fun _ r => r⟩ .id : SirM α)
      (m₂.mapOps ⟨Sum.inl, fun _ r => r⟩ .id) :=
  Bisim.mapOps (fun _ _ h => by subst h; rfl) (fun _ _ _ _ h hr => by subst h; exact hr) h

lemma bisim_refl_lift {α : Type} (m : SirM α) :
    Bisim (CallRel RI) Eq (m.mapOps ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none α)
      (m.mapOps ⟨Sum.inr, fun _ r => r⟩ .id) :=
  bisim_lift (Bisim.refl (fun _ => rfl) m)

lemma bisim_halt {α β : Type} (o : SimplifiedOutcome) :
    Bisim (OpRel.eq HostE) (fun (_ : α) (_ : β) => False) (halt o) (halt o) := by
  unfold halt
  exact Bisim.bind (Bisim.refl (fun _ => rfl) _) fun a _ _ => nomatch a

lemma bisim_ub {α β : Type} (u : UB) :
    Bisim (OpRel.eq EvalE) (fun (_ : α) (_ : β) => False) (ub u) (ub u) := by
  unfold ub
  exact Bisim.bind (Bisim.refl (fun _ => rfl) _) fun a _ _ => nomatch a

lemma bisim_evalSwitch (c : Word) (cs : Array (Word × BlockId)) (fb : Option BlockId)
    (φ : BlockId → BlockId) :
    Bisim (OpRel.eq EvalE) (fun a b => b = φ a ∧ (a ∈ cs.toList.map (·.2) ∨ fb = some a))
      (evalSwitch c cs fb) (evalSwitch c (cs.map fun (v, t) => (v, φ t)) (fb.map φ)) := by
  unfold evalSwitch
  refine Bisim.bind (Ret := fun (s₁ s₂ : Option BlockId × Unit) => s₂.1 = s₁.1.map φ ∧
      ∀ d, s₁.1 = some d → d ∈ cs.toList.map (·.2))
    (Bisim.forIn_array _ _ cs (fun a ha b₁ b₂ _ => ?_) ⟨rfl, fun _ h => nomatch h⟩) fun s₁ s₂ hs => ?_
  · obtain ⟨v, t⟩ := a
    dsimp only
    split
    · exact Bisim.pure ⟨rfl, fun d hd => by
        cases hd; exact List.mem_map.2 ⟨(v, t), Array.mem_toList_iff.2 ha, rfl⟩⟩
    · exact Bisim.pure ⟨rfl, fun _ h => nomatch h⟩
  · obtain ⟨d₁, ⟨⟩⟩ := s₁
    obtain ⟨d₂, ⟨⟩⟩ := s₂
    obtain ⟨h₁, h₂⟩ := hs
    dsimp only at h₁ h₂ ⊢
    subst h₁
    cases d₁ with
    | some d => exact Bisim.pure ⟨rfl, .inl (h₂ d rfl)⟩
    | none =>
      cases fb with
      | some d => exact Bisim.pure ⟨rfl, .inr rfl⟩
      | none => exact Bisim.mono (fun _ _ h => h.elim) (bisim_ub _)

end Leaves

section Resolve

variable (l : VarId → SirM Word) (bm : BlockId → BlockId) (fm : FunctionId → FunctionId)

lemma bisim_opResolve (op : Operation VarId) :
    Bisim (OpRel.eq EvalE) (fun o₁ o₂ => o₂ = o₁.rename fm ∧ o₁.callee? = op.callee?)
      (op.resolve l) ((op.rename fm).resolve l) := by
  cases op <;> simp only [Operation.rename, Operation.resolve] <;>
    refine Bisim.bind (Bisim.refl (fun _ => rfl) _) ?_ <;> rintro a _ rfl <;>
    exact Bisim.pure ⟨rfl, rfl⟩

lemma bisim_ctrlResolve (c : Control VarId) :
    Bisim (OpRel.eq EvalE)
      (fun c₁ c₂ => c₂ = c₁.rename bm fm ∧ c₁.targets = c.targets ∧ c₁.callee? = c.callee?)
      (c.resolve l) ((c.rename bm fm).resolve l) := by
  cases c <;> simp only [Control.rename, Control.resolve] <;>
    repeat (first
      | exact Bisim.pure ⟨rfl, rfl, rfl⟩
      | (refine Bisim.bind (Bisim.refl (fun _ => rfl) _) ?_; rintro a _ rfl))

end Resolve

section EvalFn

lemma mem_blocks' {fn : Function} {b : BlockId} {blk : Block} (h : fn[b]? = some blk) :
    blk ∈ fn.blocks :=
  Array.mem_of_getElem? h

variable (ctx ctx' : Context)

def CallMatch (i₁ i₂ : CallI) : Prop :=
  i₂ = (fnMapOf ctx.program i₁.1, i₁.2) ∧ (LiveFn ctx.program i₁.1 ∨ ctx.program[i₁.1]? = none)

def StateMatch (fn : Function) (s₁ s₂ : Option CallO × Array Word × BlockId × Vars) : Prop :=
  s₂ = (s₁.1, s₁.2.1, blockMapOf fn s₁.2.2.1, s₁.2.2.2) ∧
    (LiveBlock fn s₁.2.2.1 ∨ fn[s₁.2.2.1]? = none)

variable {ctx ctx'}

lemma bisim_noret {α β γ δ : Type} {Ret : γ → δ → Prop} (r : String)
    {g₁ : α → CoFree RecE .none γ} {g₂ : β → CoFree RecE .none δ} :
    Bisim (CallRel (CallMatch ctx)) Ret
      (((malformed r : SirM α).mapOps ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none α).bind g₁)
      (((malformed r : SirM β).mapOps ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none β).bind g₂) :=
  Bisim.bind (bisim_lift (bisim_ub _)) fun _ _ h => h.elim

lemma bisim_haltR {α β γ δ : Type} {Ret : γ → δ → Prop} (o : SimplifiedOutcome)
    {g₁ : α → CoFree RecE .none γ} {g₂ : β → CoFree RecE .none δ} :
    Bisim (CallRel (CallMatch ctx)) Ret
      ((((halt o : HostM α).mapOps ⟨Sum.inl, fun _ r => r⟩ .id : SirM α).mapOps
        ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none α).bind g₁)
      ((((halt o : HostM β).mapOps ⟨Sum.inl, fun _ r => r⟩ .id : SirM β).mapOps
        ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none β).bind g₂) :=
  Bisim.bind (bisim_lift (bisim_liftHost (bisim_halt _))) fun _ _ h => h.elim

lemma bisim_evalFn (hp : ctx'.program = ctx.program.removeDeadCode)
    (hexpr : ∀ e, Expr.eval ctx' e = Expr.eval ctx e) (hstmt : ∀ s, Stmt.exec ctx' s = Stmt.exec ctx s)
    (hcs : ctx'.checkStateful = ctx.checkStateful)
    {i₁ i₂ : CallI} (hi : CallMatch ctx i₁ i₂) :
    Bisim (OpRel.eq EvalE) Eq (evalFn ctx i₁) (evalFn ctx' i₂) := by
  unfold evalFn
  refine Bisim.fix (RI := CallMatch ctx) (fun x₁ x₂ hx => ?_) hi
  obtain ⟨f, a⟩ := x₁
  obtain ⟨hx, hl⟩ := hx
  subst hx
  dsimp only at hl ⊢
  rcases hl with hl | hnone
  · obtain ⟨fn, hfn⟩ := liveFn_some hl
    have hfn' : ctx'.program[fnMapOf ctx.program f]? = some (fn.sweep (fnMapOf ctx.program)) := by
      rw [hp]; exact removeDeadCode_live hl hfn
    rw [hfn, hfn']
    dsimp only
    refine Bisim.bind (Ret := fun (s₁ s₂ : Option CallO × Array Word × BlockId × Vars) =>
        ∃ r, s₁.1 = some r ∧ s₂.1 = some r)
      (Bisim.loop (StateMatch fn) (fun b₁ b₂ hb => ?_) ⟨rfl, liveBlock_entry fn⟩) ?_
    rotate_left
    · rintro ⟨_, _⟩ ⟨_, _⟩ ⟨r, h₁, h₂⟩
      dsimp only at h₁ h₂ ⊢
      subst h₁ h₂
      exact Bisim.pure rfl
    obtain ⟨o, inp, bi, vars⟩ := b₁
    obtain ⟨rfl, hbl⟩ := hb
    dsimp only at hbl ⊢
    rcases hbl with hbl | hbn
    · obtain ⟨blk, hblk⟩ := liveBlock_some hbl
      rw [hblk, sweep_live hbl hblk]
      dsimp only
      refine Bisim.bind (bisim_refl_lift _) ?_
      rintro vars _ rfl
      refine Bisim.bind (Bisim.forIn_array Eq (Operation.rename (fnMapOf ctx.program)) blk.ops
        (fun op hop v₁ v₂ hv => ?_) rfl) ?_
      · subst hv
        refine Bisim.bind (bisim_lift (bisim_opResolve _ _ op)) ?_
        rintro o₁ _ ⟨rfl, hco⟩
        cases o₁ with
        | «let» out e =>
          simp only [Operation.rename]
          rw [hexpr]
          refine Bisim.bind (bisim_refl_lift _) ?_
          rintro _ _ rfl
          exact Bisim.pure rfl
        | stmt st =>
          simp only [Operation.rename]
          rw [hstmt]
          refine Bisim.bind (bisim_refl_lift _) ?_
          rintro _ _ rfl
          exact Bisim.pure rfl
        | icall g args outs =>
          simp only [Operation.rename]
          refine Bisim.bind (Bisim.call (fun _ => rfl)
            ⟨rfl, liveFn_succ hl hfn hbl hblk (.inl ⟨op, hop, hco.symm⟩)⟩) ?_
          rintro _ _ rfl
          refine Bisim.bind (bisim_refl_lift _) ?_
          rintro _ _ rfl
          exact Bisim.pure rfl
      rintro vars _ rfl
      refine Bisim.bind (bisim_lift (bisim_ctrlResolve _ (blockMapOf fn) (fnMapOf ctx.program) blk.control)) ?_
      rintro c₁ _ ⟨rfl, htg, hce⟩
      have hsucc : ∀ t ∈ c₁.targets, LiveBlock fn t ∨ fn[t]? = none := fun t ht =>
        liveBlock_succ hbl hblk (htg ▸ ht)
      cases c₁ with
      | iret =>
        simp only [Control.rename]
        rw [sweep_returns]
        split
        · rename_i count _
          refine Bisim.bind (bisim_refl_lift _) ?_
          rintro outs _ rfl
          by_cases hc : count = outs.size <;> simp only [hc, ↓reduceIte]
          · exact Bisim.pure ⟨outs, rfl, rfl⟩
          · exact bisim_noret _
        · exact bisim_noret _
      | continuesTo dst =>
        simp only [Control.rename]
        refine Bisim.bind (Ret := fun b₁ b₂ => b₂ = blockMapOf fn b₁ ∧ (LiveBlock fn b₁ ∨ fn[b₁]? = none))
          (Bisim.pure ⟨rfl, hsucc _ (by simp [Control.targets])⟩) ?_
        rintro _ _ ⟨rfl, hb⟩
        refine Bisim.bind (bisim_refl_lift _) ?_
        rintro _ _ rfl
        exact Bisim.pure ⟨rfl, hb⟩
      | branches cond nz z =>
        simp only [Control.rename]
        refine Bisim.bind (Ret := fun b₁ b₂ => b₂ = blockMapOf fn b₁ ∧ (LiveBlock fn b₁ ∨ fn[b₁]? = none))
          ?_ ?_
        · split
          · exact Bisim.pure ⟨rfl, hsucc _ (by simp [Control.targets])⟩
          · exact Bisim.pure ⟨rfl, hsucc _ (by simp [Control.targets])⟩
        rintro _ _ ⟨rfl, hb⟩
        refine Bisim.bind (bisim_refl_lift _) ?_
        rintro _ _ rfl
        exact Bisim.pure ⟨rfl, hb⟩
      | switch cond cases fallback =>
        simp only [Control.rename]
        refine Bisim.bind (Ret := fun b₁ b₂ => b₂ = blockMapOf fn b₁ ∧ (LiveBlock fn b₁ ∨ fn[b₁]? = none))
          (Bisim.mono (fun b₁ b₂ ⟨h₁, h₂⟩ => ⟨h₁, hsucc _ (by
            simp only [Control.targets, List.mem_append]
            rcases h₂ with h₂ | h₂
            · exact .inl h₂
            · exact .inr (by simp [h₂]))⟩) (bisim_lift (bisim_evalSwitch _ _ _ _))) ?_
        rintro _ _ ⟨rfl, hb⟩
        refine Bisim.bind (bisim_refl_lift _) ?_
        rintro _ _ rfl
        exact Bisim.pure ⟨rfl, hb⟩
      | icallNever g args =>
        simp only [Control.rename]
        refine Bisim.bind (Bisim.call (fun _ => rfl)
          ⟨rfl, liveFn_succ hl hfn hbl hblk (.inr hce.symm)⟩) ?_
        rintro _ _ rfl
        exact bisim_noret _
      | stop => exact bisim_haltR _
      | «return» o n =>
        refine Bisim.bind (bisim_refl_lift _) ?_
        rintro _ _ rfl
        exact bisim_haltR _
      | revert o n =>
        refine Bisim.bind (bisim_refl_lift _) ?_
        rintro _ _ rfl
        exact bisim_haltR _
      | invalid => exact bisim_haltR _
      | selfdestruct b =>
        simp only [Control.rename]
        rw [hcs]
        refine Bisim.bind (bisim_refl_lift _) ?_
        rintro _ _ rfl
        exact bisim_haltR _
    · rw [hbn, sweep_none hbn]
      exact bisim_noret _
  · have hnone' : ctx'.program[fnMapOf ctx.program f]? = none := by
      rw [hp]; exact removeDeadCode_none hnone
    rw [hnone, hnone']
    exact Bisim.mono (fun _ _ h => h.elim) (bisim_lift (bisim_ub _))

lemma bisim_runInner (hp : ctx'.program = ctx.program.removeDeadCode)
    (hexpr : ∀ e, Expr.eval ctx' e = Expr.eval ctx e) (hstmt : ∀ s, Stmt.exec ctx' s = Stmt.exec ctx s)
    (hcs : ctx'.checkStateful = ctx.checkStateful) (hk : ctx'.mode.kind = ctx.mode.kind) :
    Bisim (OpRel.eq EvalE) Eq (runInner ctx) (runInner ctx') := by
  unfold runInner
  dsimp only
  rw [hk]
  cases ctx.mode.kind <;> dsimp only <;>
    refine Bisim.bind (bisim_evalFn hp hexpr hstmt hcs ⟨by rw [hp]; rfl, liveFn_root (by simp)⟩)
      fun _ _ _ => Bisim.refl (fun _ => rfl) _

end EvalFn

section Run

lemma memStep_nat {X Y : Type} (mem : MemState) (s : Step EvalE .none Empty X) (f : X → Y) :
    memStep mem (s.map f) = (memStep mem s).map fun q => (q.1, f q.2) := by
  rcases s with a | x | ⟨hop | sop, k⟩ | ⟨c, k⟩
  · exact nomatch a
  · rfl
  · rfl
  · cases sop with
    | alloc kind size =>
      simp only [Step.map, memStep]
      split
      · rfl
      split
      · congr
        funext ⟨a', _⟩
        cases kind <;> rfl
      · rfl
    | read o n =>
      simp only [Step.map, memStep]
      split
      · rfl
      · split <;> rfl
    | write o b =>
      simp only [Step.map, memStep]
      split
      · rfl
      · split <;> rfl
    | copy c =>
      obtain ⟨dst, src, len⟩ := c
      simp only [Step.map, memStep]
      split
      · rfl
      · split <;> rfl
    | ub u => rfl
  · exact nomatch c

lemma hostStep_nat {N : NonDeterminism} {A X Y : Type} (self : Address) (h : HostState)
    (s : Step HostE N A X) (f : X → Y) :
    hostStep self h (s.map f) = (hostStep self h s).map fun q => (q.1, f q.2) := by
  rcases s with a | x | ⟨op, k⟩ | ⟨c, k⟩
  · rfl
  · rfl
  · cases op <;> try rfl
    rename_i ck _ _ _
    cases ck <;> rfl
  · rfl

lemma bisim_interpMem {m₁ m₂ : SirM Empty} (h : Bisim (OpRel.eq EvalE) Eq m₁ m₂) :
    Bisim (OpRel.eq HostE) Eq (interpMem m₁) (interpMem m₂) := by
  unfold interpMem
  exact Bisim.bind (Bisim.refl (fun _ => rfl) _) fun _ _ hab => by
    subst hab; exact Bisim.interp (@memStep) memStep_nat h _

lemma bisim_interpHost {N : NonDeterminism} {A : Type} {m₁ m₂ : CoFree HostE N A}
    (h : Bisim (OpRel.eq HostE) Eq m₁ m₂) (self : Address) (w₀ : World) :
    Bisim (OpRel.eq WorldE) Eq (interpHost self w₀ m₁) (interpHost self w₀ m₂) :=
  Bisim.interp (hostStep self) (hostStep_nat self) h _

def layoutBack {p : Program} (l : Layout p.removeDeadCode) : Layout p :=
  ⟨l.init, l.init_u32, l.main, l.main_u32, l.mainStartOffset, l.initDataOffsets, l.mainDataOffsets,
   l.immutableOffsets, l.atLeastOne_immOffsets, l.no_imm_imm_overlap, l.no_imm_data_overlap⟩

def layoutFwd {p : Program} (l : Layout p) : Layout p.removeDeadCode :=
  ⟨l.init, l.init_u32, l.main, l.main_u32, l.mainStartOffset, l.initDataOffsets, l.mainDataOffsets,
   l.immutableOffsets, l.atLeastOne_immOffsets, l.no_imm_imm_overlap, l.no_imm_data_overlap⟩

lemma bisim_map {E : Effect} {N : NonDeterminism} {α β : Type} {x y : CoFree E N α} {f₁ f₂ : α → β}
    (h : Bisim (OpRel.eq E) Eq x y) (hf : ∀ a, f₁ a = f₂ a) :
    Bisim (OpRel.eq E) Eq (f₁ <$> x) (f₂ <$> y) :=
  Bisim.bind h fun a _ hab => by subst hab; exact Bisim.pure (hf a)

variable (p : Program) (l : Layout p.removeDeadCode)

lemma bisim_runInit (c : ByteArray) (e : Env) (w₀ : World) :
    Bisim (OpRel.eq WorldE) Eq (p.runInit (layoutBack l) c e w₀) (p.removeDeadCode.runInit l c e w₀) := by
  unfold Program.runInit Program.run
  refine bisim_map (bisim_interpHost (bisim_interpMem (bisim_runInner ?_ ?_ ?_ ?_ ?_)) _ _) fun o => ?_
  · rfl
  · intro ex; cases ex <;> rfl
  · intro st; cases st <;> rfl
  · rfl
  · rfl
  · rcases o with _ | (_ | _ | _ | _) <;> rfl

lemma bisim_runMain (imms : MainImmutables) (static : Bool) (cd : BytesX32) (e : Env) (w₀ : World) :
    Bisim (OpRel.eq WorldE) Eq (p.runMain (layoutBack l) imms static cd e w₀)
      (p.removeDeadCode.runMain l imms static cd e w₀) := by
  refine bisim_interpHost (bisim_interpMem (bisim_runInner ?_ ?_ ?_ ?_ ?_)) _ _
  · rfl
  · intro ex; cases ex <;> rfl
  · intro st; cases st <;> rfl
  · rfl
  · rfl

end Run

section Semantics

variable {p : Program}

lemma removeDeadCode_equiv (hs : Safe p) : Equiv p p.removeDeadCode := by
  obtain ⟨⟨⟨l⟩, _, H⟩, _⟩ := hs
  refine ⟨⟨l⟩, ⟨layoutFwd l⟩, fun l₁ l₂ e c w₀ hu => ?_⟩
  refine CoFree.Same.mono (fun a b hab => ?_) (Same.bisim (H l₁ (layoutBack l₂) e c w₀ hu) (bisim_runInit p l₂ c e w₀))
  rcases a with _ | ⟨m₁, s₁⟩ | _ | _ | _ <;> rcases b with _ | ⟨m₂, s₂⟩ | _ | _ | _ <;>
    simp only [DefinedAnd, DeployOutcomeEquiv] at hab ⊢ <;> try exact hab
  exact ⟨hab.1, fun static cd e' w => Same.bisim (hab.2 static cd e' w) (bisim_runMain p l₂ m₂ static cd e' w)⟩

lemma removeDeadCode_safe (hs : Safe p) : Safe p.removeDeadCode := by
  refine ⟨(removeDeadCode_equiv hs).symm.refl_left, fun l e c w₀ hu => ?_⟩
  obtain ⟨hdet, hret⟩ := hs.2 (layoutBack l) e c w₀ hu
  refine ⟨Deterministic.bisim hdet (bisim_runInit p l c e w₀), fun imms w' ho => ?_⟩
  obtain ⟨hwf, hms⟩ := hret imms w' (HasOutcome.bisim ho (Bisim.symm (bisim_runInit p l c e w₀)))
  exact ⟨hwf, fun e' static cd w => Deterministic.bisim (hms e' static cd w) (bisim_runMain p l imms static cd e' w)⟩

end Semantics

section Rename

variable (bm : BlockId → BlockId) (fm : FunctionId → FunctionId)

lemma op_defs_rename (op : Operation VarId) : (op.rename fm).defs = op.defs := by
  cases op <;> rfl

lemma op_reads_rename (op : Operation VarId) : (op.rename fm).reads = op.reads := by
  cases op <;> rfl

lemma ctrl_reads_rename (c : Control VarId) : (c.rename bm fm).reads = c.reads := by
  cases c <;> rfl

lemma ctrl_targets_rename {α : Type} (c : Control α) :
    (c.rename bm fm).targets = c.targets.map bm := by
  cases c with
  | switch _ _ fb => cases fb <;> simp [Control.rename, Control.targets, Function.comp_def]
  | _ => simp [Control.rename, Control.targets]

lemma ctrl_callee_rename {α : Type} (c : Control α) :
    (c.rename bm fm).callee? = c.callee?.map fm := by
  cases c <;> rfl

lemma op_callee_rename {α : Type} (op : Operation α) :
    (op.rename fm).callee? = op.callee?.map fm := by
  cases op <;> rfl

lemma block_defs_rename (b : Block) : (b.rename bm fm).defs = b.defs := by
  simp only [Block.defs, Block.rename, Array.toList_map, List.flatMap_map, op_defs_rename]

lemma block_definedBefore_rename (b : Block) (i : Nat) :
    (b.rename bm fm).definedBefore i = b.definedBefore i := by
  simp only [Block.definedBefore, Block.rename, Array.toList_map, ← List.map_take, List.flatMap_map,
    op_defs_rename]

lemma block_definedBeforeUse_rename (b : Block) (pre : List VarId) :
    (b.rename bm fm).DefinedBeforeUse pre ↔ b.DefinedBeforeUse pre := by
  unfold Block.DefinedBeforeUse
  simp only [block_definedBefore_rename]
  simp only [Block.rename, Array.size_map, Array.getElem_map, op_reads_rename, ctrl_reads_rename]

lemma block_calls_rename {b : Block} {g' : FunctionId} (h : (b.rename bm fm).Calls g') :
    ∃ g, b.Calls g ∧ g' = fm g := by
  rcases h with ⟨op', hop', hg⟩ | hg
  · simp only [Block.rename, Array.mem_map] at hop'
    obtain ⟨op, hop, rfl⟩ := hop'
    rw [op_callee_rename] at hg
    obtain ⟨g, hg', rfl⟩ := Option.map_eq_some_iff.1 hg
    exact ⟨g, .inl ⟨op, hop, hg'⟩, rfl⟩
  · simp only [Block.rename] at hg
    rw [ctrl_callee_rename] at hg
    obtain ⟨g, hg', rfl⟩ := Option.map_eq_some_iff.1 hg
    exact ⟨g, .inr hg', rfl⟩

lemma op_validIn_rename {p : Program} {k : ExecutionModeKind} {op : Operation VarId}
    (h : op.ValidIn p k) : (op.rename fm).ValidIn p.removeDeadCode k := by
  cases op <;> exact h

end Rename

section WF

variable {p : Program}

lemma keepList_flatMap_sublist {α β γ : Type} (g : α → β) (F : β → List γ) :
    ∀ (xs : List α) (ls : List Bool),
      ((keepList g xs ls).flatMap F).Sublist ((xs.map g).flatMap F)
  | x :: xs, true :: ls => by
    simp only [keepList, List.map_cons, List.flatMap_cons]
    exact (keepList_flatMap_sublist g F xs ls).append_left _
  | x :: xs, false :: ls => by
    simp only [keepList, List.map_cons, List.flatMap_cons]
    exact (keepList_flatMap_sublist g F xs ls).trans (List.sublist_append_right _ _)
  | [], _ => by simp [keepList]
  | _ :: _, [] => by simp [keepList]

lemma sweep_defs_sublist (φ : FunctionId → FunctionId) (fn : Function) :
    (fn.sweep φ).defs.Sublist fn.defs := by
  unfold Function.defs
  rw [sweep_blocks]
  have := keepList_flatMap_sublist (Block.rename (blockMapOf fn) φ) Block.defs fn.blocks.toList
    fn.liveBlocks.toList
  simpa only [List.flatMap_map, block_defs_rename] using this

lemma pathTo_back {φ : FunctionId → FunctionId} {fn : Function} (hwf : fn.WF) {prev' : List Block}
    {b' : BlockId} (h : (fn.sweep φ).PathTo prev' b') :
    ∃ prev b, fn.PathTo prev b ∧ b' = blockMapOf fn b ∧
      prev' = prev.map (Block.rename (blockMapOf fn) φ) := by
  induction h with
  | entry => exact ⟨[], fn.entry, .entry, rfl, rfl⟩
  | step _ hb' ht' ih =>
    obtain ⟨prev, b, hp, rfl, rfl⟩ := ih
    obtain ⟨b₀, blk, hl₀, hb₀, hβ, rfl⟩ := sweep_inv hb'
    obtain rfl := blockMapOf_inj hl₀ ((liveBlocks_iff fn hwf b).2 ⟨prev, hp⟩) hβ
    simp only [Block.rename, ctrl_targets_rename, List.mem_map] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    exact ⟨prev ++ [blk], t, .step hp hb₀ ht, rfl, by simp [Block.rename]⟩

lemma liveFn_of_reachable (hwf : p.WF) {r f : FunctionId} (hr : r = p.init ∨ r = p.main)
    (h : p.Reachable r f) : LiveFn p f :=
  (liveFunctions_iff p hwf f).2 (by
    rcases hr with rfl | rfl
    · exact .inl h
    · exact .inr h)

lemma callEdge_back (hwf : p.WF) {f g' : FunctionId} (hf : LiveFn p f)
    (h : p.removeDeadCode.CallEdge (fnMapOf p f) g') :
    ∃ g, p.CallEdge f g ∧ g' = fnMapOf p g := by
  obtain ⟨fn', hfn', prev', b', blk', hp', hb', hc'⟩ := h
  obtain ⟨f₀, fn, hl₀, hfn, hφ, rfl⟩ := removeDeadCode_inv hfn'
  obtain rfl := fnMapOf_inj hl₀ hf hφ
  have hfwf := hwf.functions fn (Array.mem_of_getElem? hfn)
  obtain ⟨prev, b, hp, rfl, rfl⟩ := pathTo_back hfwf hp'
  obtain ⟨b₀, blk, hlb₀, hb₀, hβ, rfl⟩ := sweep_inv hb'
  obtain rfl := blockMapOf_inj hlb₀ ((liveBlocks_iff fn hfwf b).2 ⟨prev, hp⟩) hβ
  obtain ⟨g, hc, rfl⟩ := block_calls_rename _ _ hc'
  exact ⟨g, ⟨fn, hfn, prev, b₀, blk, hp, hb₀, hc⟩, rfl⟩

lemma reachable_back (hwf : p.WF) {r f' : FunctionId} (hr : r = p.init ∨ r = p.main)
    (h : p.removeDeadCode.Reachable (fnMapOf p r) f') :
    ∃ f, p.Reachable r f ∧ f' = fnMapOf p f := by
  induction h with
  | root => exact ⟨r, .root, rfl⟩
  | call _ he ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    obtain ⟨g, hc, rfl⟩ := callEdge_back hwf (liveFn_of_reachable hwf hr hf) he
    exact ⟨g, .call hf hc, rfl⟩

lemma callee_map {f g : FunctionId} {fn : Function} {b : BlockId} {blk : Block} {n : Nat}
    {ret : ReturnKind} (hl : LiveFn p f) (hf : p[f]? = some fn) (hlb : LiveBlock fn b)
    (hb : fn[b]? = some blk) (hc : blk.Calls g) (h : p.Callee g n ret) :
    p.removeDeadCode.Callee (fnMapOf p g) n ret := by
  obtain ⟨gfn, hg, hret, e, he, hin⟩ := h
  have hlg : LiveFn p g := (liveFn_succ hl hf hlb hb hc).resolve_right (by rw [hg]; nofun)
  have hle : LiveBlock gfn gfn.entry := (liveBlock_entry gfn).resolve_right (by rw [he]; nofun)
  exact ⟨_, removeDeadCode_live hlg hg, hret, _, sweep_live hle he, hin⟩

lemma callee_map_root {r : FunctionId} (hr : r.id ∈ [p.init.id, p.main.id]) {n : Nat}
    {ret : ReturnKind} (h : p.Callee r n ret) : p.removeDeadCode.Callee (fnMapOf p r) n ret := by
  obtain ⟨gfn, hg, hret, e, he, hin⟩ := h
  have hlg : LiveFn p r := (liveFn_root hr).resolve_right (by rw [hg]; nofun)
  have hle : LiveBlock gfn gfn.entry := (liveBlock_entry gfn).resolve_right (by rw [he]; nofun)
  exact ⟨_, removeDeadCode_live hlg hg, hret, _, sweep_live hle he, hin⟩

lemma sweep_wf (φ : FunctionId → FunctionId) {fn : Function} (hwf : fn.WF) : (fn.sweep φ).WF where
  entry_valid := by
    have hle : LiveBlock fn fn.entry := (liveBlocks_iff fn hwf _).2 ⟨[], .entry⟩
    obtain ⟨blk, hb⟩ := liveBlock_some hle
    exact getElem?_lt (sweep_live (φ := φ) hle hb)
  ssa := (sweep_defs_sublist φ fn).nodup hwf.ssa
  definedBeforeUse prev' b' blk' hp' hb' := by
    obtain ⟨prev, b, hp, rfl, rfl⟩ := pathTo_back hwf hp'
    obtain ⟨b₀, blk, hlb₀, hb₀, hβ, rfl⟩ := sweep_inv hb'
    obtain rfl := blockMapOf_inj hlb₀ ((liveBlocks_iff fn hwf b).2 ⟨prev, hp⟩) hβ
    rw [block_definedBeforeUse_rename, List.flatMap_map]
    simp only [block_defs_rename]
    exact hwf.definedBeforeUse prev b₀ blk hp hb₀
  validTargets b' hb' t' ht' := by
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 hb'
    obtain ⟨b, blk, hlb, hb, _, rfl⟩ := sweep_inv (b' := ⟨i⟩) hi
    simp only [Block.rename, ctrl_targets_rename, List.mem_map] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    obtain ⟨tb, htb, hsz⟩ := hwf.validTargets blk (Array.mem_of_getElem? hb) t ht
    have hlt : LiveBlock fn t := (liveBlock_succ hlb hb ht).resolve_right (by rw [htb]; nofun)
    exact ⟨_, sweep_live hlt htb, hsz⟩
  iretArity b' hb' hc := by
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 hb'
    obtain ⟨b, blk, _, hb, _, rfl⟩ := sweep_inv (b' := ⟨i⟩) hi
    have hc' : blk.control = .iret := by
      simp only [Block.rename] at hc
      cases h : blk.control <;> rw [h] at hc <;> first | rfl | cases hc
    exact hwf.iretArity blk (Array.mem_of_getElem? hb) hc'

lemma transGen_head {α : Type} {r : α → α → Prop} {a b : α} (h : Relation.TransGen r a b) :
    ∃ c, r a c := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

lemma transGen_back (hwf : p.WF) {a' b' : FunctionId}
    (h : Relation.TransGen p.removeDeadCode.CallEdge a' b') :
    ∀ a, LiveFn p a → a' = fnMapOf p a → ∃ b, LiveFn p b ∧ b' = fnMapOf p b ∧
      Relation.TransGen p.CallEdge a b := by
  induction h with
  | single he =>
    intro a ha hφ
    subst hφ
    obtain ⟨g, hc, rfl⟩ := callEdge_back hwf ha he
    exact ⟨g, (liveFunctions_iff p hwf g).2 (((liveFunctions_iff p hwf a).1 ha).imp
      (fun h => .call h hc) (fun h => .call h hc)), rfl, .single hc⟩
  | tail _ he ih =>
    intro a ha hφ
    obtain ⟨b, hb, rfl, hab⟩ := ih a ha hφ
    obtain ⟨g, hc, rfl⟩ := callEdge_back hwf hb he
    exact ⟨g, (liveFunctions_iff p hwf g).2 (((liveFunctions_iff p hwf b).1 hb).imp
      (fun h => .call h hc) (fun h => .call h hc)), rfl, .tail hab hc⟩

lemma removeDeadCode_wf (hwf : p.WF) : p.removeDeadCode.WF where
  functions fn' hfn' := by
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 hfn'
    obtain ⟨f, fn, _, hfn, _, rfl⟩ := removeDeadCode_inv (f' := ⟨i⟩) hi
    exact sweep_wf _ (hwf.functions fn (Array.mem_of_getElem? hfn))
  validCalls fn' hfn' b' hb' := by
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 hfn'
    obtain ⟨f, fn, hlf, hfn, _, rfl⟩ := removeDeadCode_inv (f' := ⟨i⟩) hi
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 hb'
    obtain ⟨b, blk, hlb, hb, _, rfl⟩ := sweep_inv (b' := ⟨j⟩) hj
    have hv := hwf.validCalls fn (Array.mem_of_getElem? hfn) blk (Array.mem_of_getElem? hb)
    refine ⟨fun op' hop' => ?_, ?_⟩
    · simp only [Block.rename, Array.mem_map] at hop'
      obtain ⟨op, hop, rfl⟩ := hop'
      have := hv.1 op hop
      cases op with
      | icall g ins outs => exact callee_map hlf hfn hlb hb (.inl ⟨_, hop, rfl⟩) this
      | _ => trivial
    · have := hv.2
      simp only [Block.rename]
      cases h : blk.control with
      | icallNever g ins =>
        rw [h] at this
        exact callee_map hlf hfn hlb hb (.inr (by rw [h]; rfl)) this
      | _ => trivial
  initEntry := callee_map_root (by simp) hwf.initEntry
  mainEntry := callee_map_root (by simp) hwf.mainEntry
  initOps f' fn' hr hf' prev' b' blk' hp' hb' op' hop' := by
    obtain ⟨f, hrf, rfl⟩ := reachable_back hwf (.inl rfl) hr
    obtain ⟨f₀, fn, hl₀, hfn, hφ, rfl⟩ := removeDeadCode_inv hf'
    obtain rfl := fnMapOf_inj hl₀ (liveFn_of_reachable hwf (.inl rfl) hrf) hφ
    have hfwf := hwf.functions fn (Array.mem_of_getElem? hfn)
    obtain ⟨prev, b, hp, rfl, rfl⟩ := pathTo_back hfwf hp'
    obtain ⟨b₀, blk, hlb₀, hb₀, hβ, rfl⟩ := sweep_inv hb'
    obtain rfl := blockMapOf_inj hlb₀ ((liveBlocks_iff fn hfwf b).2 ⟨prev, hp⟩) hβ
    simp only [Block.rename, Array.mem_map] at hop'
    obtain ⟨op, hop, rfl⟩ := hop'
    exact op_validIn_rename _ (hwf.initOps f₀ fn hrf hfn prev b₀ blk hp hb₀ op hop)
  mainOps f' fn' hr hf' prev' b' blk' hp' hb' op' hop' := by
    obtain ⟨f, hrf, rfl⟩ := reachable_back hwf (.inr rfl) hr
    obtain ⟨f₀, fn, hl₀, hfn, hφ, rfl⟩ := removeDeadCode_inv hf'
    obtain rfl := fnMapOf_inj hl₀ (liveFn_of_reachable hwf (.inr rfl) hrf) hφ
    have hfwf := hwf.functions fn (Array.mem_of_getElem? hfn)
    obtain ⟨prev, b, hp, rfl, rfl⟩ := pathTo_back hfwf hp'
    obtain ⟨b₀, blk, hlb₀, hb₀, hβ, rfl⟩ := sweep_inv hb'
    obtain rfl := blockMapOf_inj hlb₀ ((liveBlocks_iff fn hfwf b).2 ⟨prev, hp⟩) hβ
    simp only [Block.rename, Array.mem_map] at hop'
    obtain ⟨op, hop, rfl⟩ := hop'
    exact op_validIn_rename _ (hwf.mainOps f₀ fn hrf hfn prev b₀ blk hp hb₀ op hop)
  acyclicCalls f' h := by
    obtain ⟨g', ⟨fn', hfn', _⟩⟩ := transGen_head h
    obtain ⟨f, _, hl, _, rfl, _⟩ := removeDeadCode_inv hfn'
    obtain ⟨b, hb, hφ, hfb⟩ := transGen_back hwf h f hl rfl
    obtain rfl := fnMapOf_inj hl hb hφ
    exact hwf.acyclicCalls f hfb

end WF

end Sir.Proofs.DeadCode
