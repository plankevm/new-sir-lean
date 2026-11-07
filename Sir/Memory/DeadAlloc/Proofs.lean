import Sir.Memory.DeadAlloc
import Sir.Memory.Proofs
import Sir.Passes.DeadCode.Proofs
import ITree.Refute.Theorems
import ITree.Skip.Theorems

open Host CoFree

namespace Sir.Proofs.DeadAlloc

section Fresh

lemma le_length_of_forall_mem : ∀ (n : Nat) (l : List Nat), (∀ i < n, i ∈ l) → n ≤ l.length
  | 0, _, _ => Nat.zero_le _
  | n + 1, l, h => by
    have hn : n ∈ l := h n (Nat.lt_succ_self n)
    have := le_length_of_forall_mem n (l.erase n) fun i hi =>
      (List.mem_erase_of_ne (Nat.ne_of_lt hi)).2 (h i (Nat.lt_succ_of_lt hi))
    rw [List.length_erase_of_mem hn] at this
    have : 0 < l.length := List.length_pos_of_mem hn
    omega

lemma exists_not_mem (l : List Nat) : ∃ i, i ≤ l.length ∧ i ∉ l :=
  Classical.byContradiction fun h => by
    have := le_length_of_forall_mem (l.length + 1) l fun i hi =>
      Classical.byContradiction fun hn => h ⟨i, Nat.le_of_lt_succ hi, hn⟩
    omega

lemma length_flatMap_two {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.flatMap fun r => [f r, g r]).length = 2 * l.length
  | [] => rfl
  | _ :: l => by simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, length_flatMap_two f g l]; omega

lemma exists_fresh (rs : List NatRange) (n : Nat) (hlen : rs.length ≤ 2 ^ 67)
    (hsz : ∀ r ∈ rs, r.size ≤ 2 ^ 66) (hn : n ≤ 2 ^ 66) :
    ∃ s, s + n ≤ Word.size ∧ ∀ r ∈ rs, r.Disjoint ⟨s, n⟩ := by
  obtain ⟨i, hi, hni⟩ := exists_not_mem (rs.flatMap fun r => [r.start / 2 ^ 66, r.end / 2 ^ 66])
  rw [length_flatMap_two] at hi
  refine ⟨i * 2 ^ 66, by simp only [Word.size, Word.bits]; omega, fun r hr => ?_⟩
  have h₁ : i ≠ r.start / 2 ^ 66 := fun h => hni (List.mem_flatMap.2 ⟨r, hr, by simp [h]⟩)
  have h₂ : i ≠ r.end / 2 ^ 66 := fun h => hni (List.mem_flatMap.2 ⟨r, hr, by simp [h]⟩)
  have := hsz r hr
  simp only [NatRange.Disjoint, NatRange.end] at *
  omega

end Fresh

section Machine

abbrev Triple := HostState × MemState × SirM Empty

variable (self : Address) {β : Type} (F : UB ⊕ Outcome → β)

def tstep (q : Triple) : Step WorldE MemoryND (UB ⊕ Outcome) Triple :=
  (hostStep self q.1 (memStep q.2.1 (q.2.2.step q.2.2.initial))).map
    fun p => (p.1, p.2.1, q.2.2.next p.2.2)

def W (q : Triple) : CoFree WorldE MemoryND β :=
  (CoFree.interp (hostStep self) q.1 (CoFree.interp memStep q.2.1 q.2.2)).bind
    fun r => CoFree.pure (F r)

def liftStep (G : Triple → CoFree WorldE MemoryND β) :
    Step WorldE MemoryND (UB ⊕ Outcome) Triple → Step WorldE MemoryND β (CoFree WorldE MemoryND β)
  | .pure a => .pure (F a)
  | .silent q => .silent (G q)
  | .impure op k => .impure op fun r => G (k r)
  | .branch c k => .branch c fun r => G (k r)

lemma W_observe : ∀ q : Triple, (W self F q).observe = liftStep F (W self F) (tstep self q) := by
  rintro ⟨hs, mem, ⟨S, J, s₀, step, target⟩⟩
  unfold W tstep
  rw [observe_bind, CoFree.Proofs.interp_obs]
  dsimp only [CoFree.interp]
  rw [DeadCode.hostStep_nat, Step.map_map]
  generalize hostStep self hs (memStep mem (step s₀)) = s
  rcases s with a | ⟨_, _, _ | _⟩ | ⟨op, k⟩ | ⟨c, k⟩
  · rfl
  · rfl
  · rfl
  · simp only [Step.map, liftStep, bindStep]
    congr
    funext r
    simp only [Function.comp_apply]
    rcases k r with ⟨_, _, _ | _⟩ <;> rfl
  · simp only [Step.map, liftStep, bindStep]
    congr
    funext r
    simp only [Function.comp_apply]
    rcases k r with ⟨_, _, _ | _⟩ <;> rfl

lemma tstep_silent {hs : HostState} {mem : MemState} {m n : SirM Empty} (h : m.observe = .silent n) :
    tstep self (hs, mem, m) = .silent (hs, mem, n) := by
  unfold tstep
  unfold observe at h
  generalize hs' : m.step m.initial = s at h
  rcases s <;> simp only [Step.map, Step.silent.injEq, reduceCtorEq] at h
  subst h
  rfl

lemma tstep_impure {hs : HostState} {mem : MemState} {m : SirM Empty} {op : EvalE.Op}
    {k : EvalE.Resp op → SirM Empty} (h : m.observe = .impure op k) :
    tstep self (hs, mem, m) =
      (hostStep self hs (memStep mem (.impure op id))).map fun p => (p.1, p.2.1, k p.2.2) := by
  unfold tstep
  unfold observe at h
  generalize hs' : m.step m.initial = s at h
  rcases s <;> simp only [Step.map, Step.impure.injEq, reduceCtorEq] at h
  rename_i op' k'
  obtain ⟨rfl, h⟩ := h
  cases h
  rw [show (Step.impure op' k' : Step EvalE .none Empty _) = (Step.impure op' id).map k' from rfl,
    DeadCode.memStep_nat, DeadCode.hostStep_nat, Step.map_map]
  rfl

lemma observe_cases (m : SirM Empty) :
    (∃ n, m.observe = .silent n) ∨ ∃ op k, m.observe = .impure op k := by
  generalize h : m.observe = s
  rcases s with a | n | ⟨op, k⟩ | ⟨c, _⟩
  · exact nomatch a
  · exact .inl ⟨n, rfl⟩
  · exact .inr ⟨op, k, rfl⟩
  · exact nomatch c

end Machine

section State

structure MemInv (m : MemState) : Prop where
  pairwise : m.taken.Pairwise NatRange.Disjoint
  pos : ∀ r ∈ m.taken, 0 < r.size
  small : ∀ r ∈ m.taken, r.size ≤ 2 ^ 64
  count : m.taken.length ≤ m.cumAlloced.toNat + 1
  bound : ∀ r ∈ m.taken, r.end ≤ Word.size
  sum : (m.taken.map NatRange.size).sum = m.cumAlloced.toNat + CompilerReservedBytes

def Sub (L L' : List NatRange) : Prop := ∀ r ∈ L, r ∈ L'

def Small (L : List NatRange) : Prop := L.length ≤ 2 ^ 66 ∧ ∀ r ∈ L, r.size ≤ 2 ^ 64

def Avoids (L : List NatRange) (a : Allocation) : Prop := ∀ r ∈ L, r.Disjoint a.range

structure MemCorr (L : List NatRange) (m₁ m₂ : MemState) : Prop where
  reserved : m₁.reserved = m₂.reserved
  cum : m₂.cumAlloced.toNat ≤ m₁.cumAlloced.toNat
  dead : ∃ D : List Allocation, m₁.live.toList.Perm (m₂.live.toList ++ D) ∧ ∀ d ∈ D, Avoids L d

structure Corr (L : List NatRange) (q₁ q₂ : Triple) : Prop where
  host : q₁.1 = q₂.1
  mem : MemCorr L q₁.2.1 q₂.2.1
  inv₁ : MemInv q₁.2.1
  inv₂ : MemInv q₂.2.1
  skip : Skip DeadExtra (fun _ => False) Eq q₁.2.2 q₂.2.2

def faultPts {X : Type 1} : Step EvalE .none Empty X → List NatRange
  | .impure (.inr (.read o _)) _ => [⟨o.toNat, 1⟩]
  | .impure (.inr (.write o _)) _ => [⟨o.toNat, 1⟩]
  | .impure (.inr (.copy c)) _ => [⟨c.src.toNat, 1⟩, ⟨c.dst.toNat, 1⟩]
  | _ => []

def TRel (L : List NatRange) (cov : Prop) (s₁ s₂ : Step WorldE MemoryND (UB ⊕ Outcome) Triple) : Prop :=
  (∃ u, s₁ = .pure (.inl u)) ∨
  match s₂ with
  | .pure b => cov → s₁ = .pure b
  | .silent q₂ => ∃ q₁, s₁ = .silent q₁ ∧ Corr L q₁ q₂
  | .impure op k₂ => ∃ k₁, s₁ = .impure op k₁ ∧ ∀ r, Corr L (k₁ r) (k₂ r)
  | .branch _ k₂ => ∃ c k₁, s₁ = .branch c k₁ ∧
      ∀ r₂, Sub (k₂ r₂).2.1.taken L → ∃ r₁, Corr L (k₁ r₁) (k₂ r₂)

end State

section Mem

open Classical

lemma mem_taken_of_live {m : MemState} {a : Allocation} (h : a ∈ m.live.toList) : a.range ∈ m.taken :=
  List.mem_cons_of_mem _ (List.mem_map_of_mem h)

lemma disjoint_symm {a b : NatRange} (h : a.Disjoint b) : b.Disjoint a := by
  simp only [NatRange.Disjoint] at *; omega

lemma live_pairwise {m : MemState} (hI : MemInv m) :
    m.live.toList.Pairwise fun a b => a.range.Disjoint b.range :=
  List.pairwise_map.1 (List.pairwise_cons.1 hI.pairwise).2

lemma pairwise_rel {α : Type} {R : α → α → Prop} (hsymm : ∀ {a b}, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact hp.1 _ hb'
    · exact hsymm (hp.1 _ ha')
    · exact pairwise_rel hsymm hp.2 ha' hb' hne

lemma live_nodup {m : MemState} (hI : MemInv m) : m.live.toList.Nodup :=
  (live_pairwise hI).imp_of_mem fun ha _ hd heq => by
    subst heq
    have := hI.pos _ (mem_taken_of_live ha)
    simp only [NatRange.Disjoint, NatRange.end] at hd
    omega

def Contains (a : Allocation) (o : Word) (len : Nat) : Prop :=
  a.start.toNat ≤ o.toNat ∧ o.toNat + len ≤ a.end

lemma region_unique {m : MemState} (hI : MemInv m) {o : Word} {len : Nat} (hlen : 0 < len)
    (r : m.Region o len) {a : Allocation} (ha : a ∈ m.live.toList) (hc : Contains a o len) :
    m.live[r.val] = a := by
  refine Classical.byContradiction fun hne => ?_
  have hd := pairwise_rel (fun h => disjoint_symm h) (live_pairwise hI)
    (Array.getElem_mem_toList r.val.isLt) ha hne
  have := r.property
  simp only [Contains, NatRange.Disjoint, NatRange.end, Allocation.range, Allocation.end,
    Allocation.size, Fin.getElem_fin] at *
  omega

lemma inBounds_none {m : MemState} {o : Word} {len : Nat} (h : m.inBounds o len = none) :
    ∀ a ∈ m.live.toList, ¬Contains a o len := by
  intro a ha hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  unfold MemState.inBounds at h
  have hj' : j < m.allocCount := by simpa [MemState.allocCount] using hj
  have := List.findSome?_eq_none_iff.1 h ⟨j, hj'⟩ (List.mem_finRange _)
  simp only [Fin.getElem_fin, dite_eq_right_iff, reduceCtorEq, imp_false] at this
  exact this (by simpa [Contains] using hc)

lemma inBounds_some_of {m : MemState} {o : Word} {len : Nat} {a : Allocation}
    (ha : a ∈ m.live.toList) (hc : Contains a o len) : ∃ r, m.inBounds o len = some r := by
  cases h : m.inBounds o len with
  | none => exact absurd hc (inBounds_none h a ha)
  | some r => exact ⟨r, rfl⟩

lemma region_contains {m : MemState} {o : Word} {len : Nat} (r : m.Region o len) :
    Contains m.live[r.val] o len := r.property

lemma read_congr {m₁ m₂ : MemState} {o : Word} {len : Nat} (r₁ : m₁.Region o len)
    (r₂ : m₂.Region o len) (h : m₁.live[r₁.val] = m₂.live[r₂.val]) : m₁.read r₁ = m₂.read r₂ := by
  simp only [MemState.read, h]

lemma modify_eq_map {α : Type} (f : α → α) (a : α) : ∀ (l : List α) (i : Nat) (hi : i < l.length),
    l.Nodup → l[i] = a → l.modify i f = l.map fun b => if b = a then f b else b
  | [], _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | b :: l, 0, _, hn, ha => by
    simp only [List.getElem_cons_zero] at ha
    subst ha
    rw [List.modify_zero_cons, List.map_cons]
    simp only [ite_true]
    congr 1
    refine ((List.map_congr_left fun c hc => ?_).trans (List.map_id _)).symm
    have : c ≠ b := fun h => (List.nodup_cons.1 hn).1 (h ▸ hc)
    simp [this]
  | b :: l, i + 1, hi, hn, ha => by
    simp only [List.getElem_cons_succ] at ha
    have hi' : i < l.length := by simpa using hi
    rw [List.modify_succ_cons, List.map_cons]
    have hne : b ≠ a := fun h => (List.nodup_cons.1 hn).1 (h ▸ ha ▸ List.getElem_mem hi')
    simp only [hne, ite_false]
    rw [modify_eq_map f a l i hi' (List.nodup_cons.1 hn).2 ha]

lemma write_live (m : MemState) {o : Word} {len : Nat} (bytes : ByteArray) (r : m.Region o len) :
    (m.write bytes r).live.toList = m.live.toList.modify r.val
      (fun a => { a with bytes := bytes.copySlice 0 a.bytes (o - a.start).toNat len }) := by
  simp only [MemState.write, Array.toList_modify]

lemma inv_write {m : MemState} (hI : MemInv m) {o : Word} {len : Nat} (bytes : ByteArray)
    (r : m.Region o len) : MemInv (m.write bytes r) where
  pairwise := by rw [taken_write]; exact hI.pairwise
  pos := by rw [taken_write]; exact hI.pos
  small := by rw [taken_write]; exact hI.small
  count := by rw [taken_write]; exact hI.count
  bound := by rw [taken_write]; exact hI.bound
  sum := by rw [taken_write]; exact hI.sum

lemma cum_push (m : MemState) (a : Allocation) (h : m.cumAlloced.toNat + a.size < 2 ^ 64) :
    (m.push a).cumAlloced.toNat = m.cumAlloced.toNat + a.size := by
  simp only [MemState.push, UInt64.toNat_add, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (a := a.size) (by omega), Nat.mod_eq_of_lt h]

lemma taken_push (m : MemState) (a : Allocation) : (m.push a).taken = m.taken ++ [a.range] := by
  simp [MemState.taken, MemState.push]

lemma inv_push {m : MemState} {a : Allocation} (hI : MemInv m) (hv : ∀ r ∈ m.taken, r.Disjoint a.range)
    (hpos : 0 < a.size) (hcum : m.cumAlloced.toNat + a.size < 2 ^ 64) (hend : a.end ≤ Word.size) :
    MemInv (m.push a) where
  pairwise := by
    rw [taken_push, List.pairwise_append]
    exact ⟨hI.pairwise, List.pairwise_singleton _ _, fun r hr _ hb => (List.mem_singleton.1 hb) ▸ hv r hr⟩
  pos := by
    rw [taken_push]
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hI.pos r hr
    · rw [List.mem_singleton.1 hr]; exact hpos
  small := by
    rw [taken_push]
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hI.small r hr
    · rw [List.mem_singleton.1 hr]; simp only [Allocation.range]; omega
  count := by
    rw [taken_push, cum_push m a hcum, List.length_append, List.length_singleton]
    have := hI.count
    omega
  bound := by
    rw [taken_push]
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hI.bound r hr
    · rw [List.mem_singleton.1 hr]; exact hend
  sum := by
    rw [taken_push, cum_push m a hcum, List.map_append, List.sum_append, hI.sum]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Allocation.range]
    omega

lemma inv_init (s : Nat) (hs : s < Word.size - CompilerReservedBytes) :
    MemInv { reserved := ⟨s, CompilerReservedBytes⟩ } where
  pairwise := by simp [MemState.taken]
  pos := by simp [MemState.taken, CompilerReservedBytes]
  small := by simp [MemState.taken, CompilerReservedBytes]
  count := by simp [MemState.taken]
  bound := by
    intro r hr
    simp only [MemState.taken, List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp only [NatRange.end, Word.size, Word.bits, CompilerReservedBytes] at *
      omega
    · simp at hr
  sum := by simp [MemState.taken]

lemma sum_filter {α : Type} (f : α → Nat) (p : α → Bool) : ∀ l : List α,
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter fun a => !p a).map f).sum
  | [] => rfl
  | a :: l => by
    have := sum_filter f p l
    cases h : p a <;> simp [h] <;> omega

lemma sum_le : ∀ (n : Nat) (l : List NatRange) (lo hi : Nat), l.length ≤ n →
    l.Pairwise NatRange.Disjoint → (∀ r ∈ l, lo ≤ r.start ∧ r.end ≤ hi) → (l.map NatRange.size).sum + lo ≤ hi ∨ l = []
  | _, [], _, _, _, _, _ => .inr rfl
  | 0, _ :: _, _, _, h, _, _ => absurd h (by simp)
  | n + 1, r :: rest, lo, hi, hlen, hp, hb => by
    left
    rw [List.pairwise_cons] at hp
    have hlr := hb r List.mem_cons_self
    let p : NatRange → Bool := fun r' => decide (r'.end ≤ r.start)
    have hB := sum_le n (rest.filter p) lo r.start
      (Nat.le_trans (List.length_filter_le _ _) (by simpa using hlen)) (hp.2.filter _) fun r' hr' => by
        obtain ⟨hr', hpr⟩ := List.mem_filter.1 hr'
        exact ⟨(hb r' (List.mem_cons_of_mem _ hr')).1, of_decide_eq_true hpr⟩
    have hA := sum_le n (rest.filter fun a => !p a) r.end hi
      (Nat.le_trans (List.length_filter_le _ _) (by simpa using hlen)) (hp.2.filter _) fun r' hr' => by
        obtain ⟨hr', hpr⟩ := List.mem_filter.1 hr'
        have hd := hp.1 r' hr'
        simp only [p, Bool.not_eq_true', decide_eq_false_iff_not] at hpr
        simp only [NatRange.Disjoint] at hd
        exact ⟨by omega, (hb r' (List.mem_cons_of_mem _ hr')).2⟩
    have hB' : ((rest.filter p).map NatRange.size).sum + lo ≤ r.start := by
      rcases hB with h | h
      · exact h
      · rw [h]; simp only [List.map_nil, List.sum_nil]; omega
    have hA' : ((rest.filter fun a => !p a).map NatRange.size).sum + r.end ≤ hi := by
      rcases hA with h | h
      · exact h
      · rw [h]; simp only [List.map_nil, List.sum_nil]; omega
    rw [List.map_cons, List.sum_cons, sum_filter _ p rest]
    simp only [NatRange.end] at hlr hB' hA' ⊢
    omega

lemma no_wrap {m : MemState} (hI : MemInv m) {n : Nat} {a : Allocation} (hv : m.ValidAlloc n a)
    (hpos : 0 < n) : m.cumAlloced.toNat + CompilerReservedBytes + n ≤ Word.size := by
  obtain ⟨hsz, hend, hd⟩ := hv
  have hp : (m.taken ++ [a.range]).Pairwise NatRange.Disjoint := by
    rw [List.pairwise_append]
    exact ⟨hI.pairwise, List.pairwise_singleton _ _, fun r hr _ hb => (List.mem_singleton.1 hb) ▸ hd hpos r hr⟩
  rcases sum_le _ (m.taken ++ [a.range]) 0 Word.size (Nat.le_refl _) hp (fun r hr => by
      rcases List.mem_append.1 hr with hr | hr
      · exact ⟨Nat.zero_le _, hI.bound r hr⟩
      · rw [List.mem_singleton.1 hr]; exact ⟨Nat.zero_le _, hend⟩) with h | h
  · rw [List.map_append, List.sum_append, hI.sum] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Allocation.range, hsz] at h
    omega
  · simp at h

lemma corr_init (L : List NatRange) (m : MemState) : MemCorr L m m :=
  ⟨rfl, Nat.le_refl _, [], by simp, by simp⟩

lemma corr_live {L : List NatRange} {m₁ m₂ : MemState} (hc : MemCorr L m₁ m₂) {a : Allocation}
    (ha : a ∈ m₁.live.toList) : a ∈ m₂.live.toList ∨ Avoids L a := by
  obtain ⟨D, hp, hD⟩ := hc.dead
  rcases List.mem_append.1 (hp.mem_iff.1 ha) with h | h
  · exact .inl h
  · exact .inr (hD a h)

lemma corr_live₂ {L : List NatRange} {m₁ m₂ : MemState} (hc : MemCorr L m₁ m₂) {a : Allocation}
    (ha : a ∈ m₂.live.toList) : a ∈ m₁.live.toList := by
  obtain ⟨D, hp, _⟩ := hc.dead
  exact hp.mem_iff.2 (List.mem_append_left _ ha)

lemma corr_sub {L : List NatRange} {m₁ m₂ : MemState} (hc : MemCorr L m₁ m₂) : Sub m₂.taken m₁.taken := by
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr
  · rw [← hc.reserved]; exact List.mem_cons_self
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    exact mem_taken_of_live (corr_live₂ hc ha)

lemma corr_write {L : List NatRange} {m₁ m₂ : MemState} (hc : MemCorr L m₁ m₂) (hI₁ : MemInv m₁)
    {o : Word} {len : Nat} (bytes : ByteArray) (r₁ : m₁.Region o len) (r₂ : m₂.Region o len)
    (h : m₁.live[r₁.val] = m₂.live[r₂.val]) : MemCorr L (m₁.write bytes r₁) (m₂.write bytes r₂) := by
  obtain ⟨D, hp, hD⟩ := hc.dead
  refine ⟨hc.reserved, hc.cum, D, ?_, hD⟩
  rw [write_live, write_live]
  have hn₁ := live_nodup hI₁
  have hn := hp.nodup_iff.1 hn₁
  have hn₂ := (List.nodup_append.1 hn).1
  generalize hf : (fun a : Allocation => { a with bytes := bytes.copySlice 0 a.bytes (o - a.start).toNat len }) = f
  have ha₂ : m₂.live.toList[r₂.val.val]'(by simp) = m₂.live[r₂.val] := by simp
  have ha₁ : m₁.live.toList[r₁.val.val]'(by simp) = m₂.live[r₂.val] := by simpa using h
  rw [modify_eq_map f _ _ _ (by simp) hn₁ ha₁, modify_eq_map f _ _ _ (by simp) hn₂ ha₂]
  have hD' : D.map (fun b => if b = m₂.live[r₂.val] then f b else b) = D := by
    refine (List.map_congr_left fun d hd => ?_).trans (List.map_id _)
    have : d ≠ m₂.live[r₂.val] := fun he =>
      (List.nodup_append.1 hn).2.2 _ (Array.getElem_mem_toList _) _ hd he.symm
    simp only [this, ite_false]
    rfl
  have := hp.map (fun b => if b = m₂.live[r₂.val] then f b else b)
  rw [List.map_append, hD'] at this
  exact this

lemma corr_push {L : List NatRange} {m₁ m₂ : MemState} (hc : MemCorr L m₁ m₂) (a : Allocation)
    (h₁ : m₁.cumAlloced.toNat + a.size < 2 ^ 64) (h₂ : m₂.cumAlloced.toNat + a.size < 2 ^ 64) :
    MemCorr L (m₁.push a) (m₂.push a) := by
  obtain ⟨D, hp, hD⟩ := hc.dead
  refine ⟨hc.reserved, by rw [cum_push _ _ h₁, cum_push _ _ h₂]; have := hc.cum; omega, D, ?_, hD⟩
  simp only [MemState.push, Array.toList_push]
  exact (hp.append_right _).trans (by
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm)

lemma corr_push_dead {L : List NatRange} {m₁ m₂ : MemState} (hc : MemCorr L m₁ m₂) (a : Allocation)
    (h₁ : m₁.cumAlloced.toNat + a.size < 2 ^ 64) (hav : Avoids L a) : MemCorr L (m₁.push a) m₂ := by
  obtain ⟨D, hp, hD⟩ := hc.dead
  refine ⟨hc.reserved, by rw [cum_push _ _ h₁]; have := hc.cum; omega, D ++ [a], ?_, ?_⟩
  · simp only [MemState.push, Array.toList_push, ← List.append_assoc]
    exact hp.append_right _
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hD d hd
    · rw [List.mem_singleton.1 hd]; exact hav

end Mem

section Steps

variable (self : Address)

def post (hs : HostState) {R : Type} (k : R → SirM Empty) (s : Step HostE MemoryND UB (MemState × R)) :
    Step WorldE MemoryND (UB ⊕ Outcome) Triple :=
  (hostStep self hs s).map fun p => (p.1, p.2.1, k p.2.2)

lemma tstep_post {hs : HostState} {mem : MemState} {m : SirM Empty} {op : EvalE.Op}
    {k : EvalE.Resp op → SirM Empty} (h : m.observe = .impure op k) :
    tstep self (hs, mem, m) = post self hs k (memStep mem (.impure op id)) :=
  tstep_impure self h

variable {self} {L : List NatRange} {cov : Prop}

lemma trel_bad {u : UB} {s₂ : Step WorldE MemoryND (UB ⊕ Outcome) Triple} :
    TRel L cov (.pure (.inl u)) s₂ := .inl ⟨u, rfl⟩

lemma trel_silent {q₁ q₂ : Triple} (h : Corr L q₁ q₂) : TRel L cov (.silent q₁) (.silent q₂) :=
  .inr ⟨q₁, rfl, h⟩

lemma trel_pure {s₁ : Step WorldE MemoryND (UB ⊕ Outcome) Triple} {b : UB ⊕ Outcome}
    (h : cov → s₁ = .pure b) : TRel L cov s₁ (.pure b) := .inr h

lemma trel_impure {op : WorldE.Op} {k₁ k₂ : WorldE.Resp op → Triple} (h : ∀ r, Corr L (k₁ r) (k₂ r)) :
    TRel L cov (.impure op k₁) (.impure op k₂) := .inr ⟨k₁, rfl, h⟩

lemma trel_branch {c₁ c₂ : MemoryND.Op} {k₁ : MemoryND.Resp c₁ → Triple} {k₂ : MemoryND.Resp c₂ → Triple}
    (h : ∀ r₂, Sub (k₂ r₂).2.1.taken L → ∃ r₁, Corr L (k₁ r₁) (k₂ r₂)) :
    TRel L cov (.branch c₁ k₁) (.branch c₂ k₂) := .inr ⟨c₁, k₁, rfl, h⟩

lemma trel_map {X : Type} (S : Step WorldE MemoryND (UB ⊕ Outcome) X) {f₁ f₂ : X → Triple}
    (h : ∀ x, Corr L (f₁ x) (f₂ x)) : TRel L cov (S.map f₁) (S.map f₂) := by
  rcases S with b | x | ⟨op, k⟩ | ⟨c, k⟩
  · exact trel_pure fun _ => rfl
  · exact trel_silent (h x)
  · exact trel_impure fun r => h (k r)
  · exact trel_branch fun r _ => ⟨r, h (k r)⟩

variable {hs : HostState} {mem₁ mem₂ : MemState}

lemma fault_contra (hc : MemCorr L mem₁ mem₂) {o : Word} {len : Nat} (hlen : 0 < len)
    (h₂ : mem₂.inBounds o len = none) (hcov : ⟨o.toNat, 1⟩ ∈ L) (r₁ : mem₁.Region o len) : False := by
  rcases corr_live hc (Array.getElem_mem_toList r₁.val.isLt) with h | h
  · exact inBounds_none h₂ _ h (region_contains r₁)
  · have hd := h _ hcov
    have hcn := region_contains r₁
    simp only [Contains, NatRange.Disjoint, NatRange.end, Allocation.range, Allocation.end,
      Allocation.size, Fin.getElem_fin] at hd hcn
    omega

lemma region_match (hc : MemCorr L mem₁ mem₂) (hI₁ : MemInv mem₁) {o : Word} {len : Nat} (hlen : 0 < len)
    (r₁ : mem₁.Region o len) (r₂ : mem₂.Region o len) : mem₁.live[r₁.val] = mem₂.live[r₂.val] :=
  (region_unique hI₁ hlen r₁ (corr_live₂ hc (Array.getElem_mem_toList _)) (region_contains r₂)).symm ▸ rfl

lemma word_pos {w : Word} (h : ¬w = 0) : 0 < w.toNat :=
  Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))

variable {R : Type} {k₁ k₂ : R → SirM Empty}

lemma match_read (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (i₂ : MemInv mem₂) (o len : Word)
    {k₁ k₂ : ByteArray → SirM Empty} (hk : ∀ r, Skip DeadExtra (fun _ => False) Eq (k₁ r) (k₂ r)) :
    TRel L (Sub [⟨o.toNat, 1⟩] L) (post self hs k₁ (memStep mem₁ (.impure (.inr (.read o len)) id)))
      (post self hs k₂ (memStep mem₂ (.impure (.inr (.read o len)) id))) := by
  simp only [memStep]
  by_cases h0 : len = 0
  · simp only [h0, ↓reduceIte, post, hostStep, Step.map]
    exact trel_silent ⟨rfl, hc, i₁, i₂, hk _⟩
  · have hlen := word_pos h0
    simp only [h0, ↓reduceIte]
    cases h₁ : mem₁.inBounds o len.toNat with
    | none => exact trel_bad
    | some r₁ =>
      cases h₂ : mem₂.inBounds o len.toNat with
      | none =>
        exact trel_pure fun hcov => (fault_contra hc hlen h₂ (hcov _ List.mem_cons_self) r₁).elim
      | some r₂ =>
        simp only [post, hostStep, Step.map]
        rw [read_congr r₁ r₂ (region_match hc i₁ hlen r₁ r₂)]
        exact trel_silent ⟨rfl, hc, i₁, i₂, hk _⟩

lemma match_write (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (i₂ : MemInv mem₂) (o : Word)
    (bytes : ByteArray) {k₁ k₂ : Unit → SirM Empty}
    (hk : ∀ r, Skip DeadExtra (fun _ => False) Eq (k₁ r) (k₂ r)) :
    TRel L (Sub [⟨o.toNat, 1⟩] L) (post self hs k₁ (memStep mem₁ (.impure (.inr (.write o bytes)) id)))
      (post self hs k₂ (memStep mem₂ (.impure (.inr (.write o bytes)) id))) := by
  simp only [memStep]
  by_cases h0 : bytes.size = 0
  · simp only [h0, ↓reduceIte, post, hostStep, Step.map]
    exact trel_silent ⟨rfl, hc, i₁, i₂, hk _⟩
  · have hlen : 0 < bytes.size := Nat.pos_of_ne_zero h0
    simp only [h0, ↓reduceIte]
    cases h₁ : mem₁.inBounds o bytes.size with
    | none => exact trel_bad
    | some r₁ =>
      cases h₂ : mem₂.inBounds o bytes.size with
      | none =>
        exact trel_pure fun hcov => (fault_contra hc hlen h₂ (hcov _ List.mem_cons_self) r₁).elim
      | some r₂ =>
        simp only [post, hostStep, Step.map]
        exact trel_silent ⟨rfl, corr_write hc i₁ bytes r₁ r₂ (region_match hc i₁ hlen r₁ r₂),
          inv_write i₁ bytes r₁, inv_write i₂ bytes r₂, hk _⟩

lemma match_copy (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (i₂ : MemInv mem₂) (dst src len : Word)
    {k₁ k₂ : Unit → SirM Empty} (hk : ∀ r, Skip DeadExtra (fun _ => False) Eq (k₁ r) (k₂ r)) :
    TRel L (Sub [⟨src.toNat, 1⟩, ⟨dst.toNat, 1⟩] L)
      (post self hs k₁ (memStep mem₁ (.impure (.inr (.copy ⟨dst, src, len⟩)) id)))
      (post self hs k₂ (memStep mem₂ (.impure (.inr (.copy ⟨dst, src, len⟩)) id))) := by
  simp only [memStep]
  by_cases h0 : len = 0
  · simp only [h0, ↓reduceIte, post, hostStep, Step.map]
    exact trel_silent ⟨rfl, hc, i₁, i₂, hk _⟩
  · have hlen := word_pos h0
    simp only [h0, ↓reduceIte]
    cases h₁ : mem₁.inBounds src len.toNat with
    | none => exact trel_bad
    | some r₁ =>
      cases h₁' : mem₁.inBounds dst len.toNat with
      | none => exact trel_bad
      | some w₁ =>
        cases h₂ : mem₂.inBounds src len.toNat with
        | none =>
          exact trel_pure fun hcov => (fault_contra hc hlen h₂ (hcov _ List.mem_cons_self) r₁).elim
        | some r₂ =>
          cases h₂' : mem₂.inBounds dst len.toNat with
          | none =>
            exact trel_pure fun hcov =>
              (fault_contra hc hlen h₂' (hcov _ (List.mem_cons_of_mem _ List.mem_cons_self)) w₁).elim
          | some w₂ =>
            simp only [post, hostStep, Step.map]
            rw [read_congr r₁ r₂ (region_match hc i₁ hlen r₁ r₂)]
            exact trel_silent ⟨rfl, corr_write hc i₁ _ w₁ w₂ (region_match hc i₁ hlen w₁ w₂),
              inv_write i₁ _ w₁, inv_write i₂ _ w₂, hk _⟩

lemma match_ub (u : UB) {k₁ k₂ : Empty → SirM Empty} :
    TRel L cov (post self hs k₁ (memStep mem₁ (.impure (.inr (.ub u)) id)))
      (post self hs k₂ (memStep mem₂ (.impure (.inr (.ub u)) id))) := trel_bad

lemma match_host (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (i₂ : MemInv mem₂) (op : HostOp)
    {k₁ k₂ : HostE.Resp op → SirM Empty} (hk : ∀ r, Skip DeadExtra (fun _ => False) Eq (k₁ r) (k₂ r)) :
    TRel L cov (post self hs k₁ (memStep mem₁ (.impure (.inl op) id)))
      (post self hs k₂ (memStep mem₂ (.impure (.inl op) id))) := by
  have e : ∀ (mem : MemState) (k : HostE.Resp op → SirM Empty),
      post self hs k (memStep mem (.impure (.inl op) id)) =
        (hostStep self hs (.impure op id : Step HostE MemoryND UB (HostE.Resp op))).map
          fun p => (p.1, mem, k p.2) := by
    intro mem k
    have h2 : hostStep self hs (.impure op fun r => (mem, r) : Step HostE MemoryND UB _) =
        (hostStep self hs (.impure op id : Step HostE MemoryND UB (HostE.Resp op))).map
          fun p => (p.1, (mem, p.2)) :=
      DeadCode.hostStep_nat self hs (.impure op id) (fun r => (mem, r))
    unfold post
    simp only [memStep, id]
    rw [h2, Step.map_map]
  rw [e, e]
  exact trel_map _ fun p => ⟨rfl, hc, i₁, i₂, hk _⟩

lemma zeroed_size (a : Allocation) :
    ({ start := a.start, bytes := ⟨.replicate a.size 0⟩ } : Allocation).size = a.size := by
  simp only [Allocation.size, ByteArray.size, Array.size_replicate]

lemma zeroed_range (a : Allocation) :
    ({ start := a.start, bytes := ⟨.replicate a.size 0⟩ } : Allocation).range = a.range := by
  unfold Allocation.range
  rw [zeroed_size]

lemma check_iff {c : Nat} {size : Word} (hc : c + size.toNat < Word.size) :
    ((c : Word) + size ≥ (UInt64.size : Word)) ↔ 2 ^ 64 ≤ c + size.toNat := by
  simp only [Word.size, Word.bits] at hc
  simp only [GE.ge, BitVec.le_def, BitVec.toNat_add, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    UInt64.size]
  rw [Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt hc]

lemma valid_of_corr (hc : MemCorr L mem₁ mem₂) {n : Nat} {a : Allocation} (hv : mem₁.ValidAlloc n a) :
    mem₂.ValidAlloc n a :=
  ⟨hv.1, hv.2.1, fun hp r hr => hv.2.2 hp r (corr_sub hc r hr)⟩

lemma corr_alloc (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (i₂ : MemInv mem₂) {A : Allocation}
    {size : Word} (hsz : A.size = size.toNat) (hend : A.end ≤ Word.size)
    (hv₁ : 0 < size.toNat → ∀ r ∈ mem₁.taken, r.Disjoint A.range)
    (hv₂ : 0 < size.toNat → ∀ r ∈ mem₂.taken, r.Disjoint A.range)
    (hn₁ : mem₁.cumAlloced.toNat + size.toNat < 2 ^ 64)
    {m₁ m₂ : SirM Empty} (hk : Skip DeadExtra (fun _ => False) Eq m₁ m₂) :
    Corr L (hs, if size > 0 then mem₁.push A else mem₁, m₁) (hs, if size > 0 then mem₂.push A else mem₂, m₂) := by
  by_cases hp : size > 0
  · have hp' : 0 < size.toNat := by simpa [BitVec.lt_def] using hp
    have hn₂ : mem₂.cumAlloced.toNat + A.size < 2 ^ 64 := by have := hc.cum; omega
    simp only [hp, ↓reduceIte]
    exact ⟨rfl, corr_push hc A (by omega) hn₂, inv_push i₁ (hv₁ hp') (by omega) (by omega) hend,
      inv_push i₂ (hv₂ hp') (by omega) hn₂ hend, hk⟩
  · simp only [hp, ↓reduceIte]
    exact ⟨rfl, hc, i₁, i₂, hk⟩

lemma match_alloc (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (i₂ : MemInv mem₂) (kind : AllocKind)
    (size : Word) {k₁ k₂ : Word → SirM Empty} (hk : ∀ r, Skip DeadExtra (fun _ => False) Eq (k₁ r) (k₂ r)) :
    TRel L cov (post self hs k₁ (memStep mem₁ (.impure (.inr (.alloc kind size)) id)))
      (post self hs k₂ (memStep mem₂ (.impure (.inr (.alloc kind size)) id))) := by
  simp only [memStep]
  by_cases hck₁ : (mem₁.cumAlloced.toNat : Word) + size ≥ (UInt64.size : Word)
  · simp only [hck₁, ↓reduceIte, post, hostStep, Step.map]; exact trel_bad
  by_cases hnv : ¬∃ a', mem₁.ValidAlloc size.toNat a'
  · simp only [hck₁, hnv, ↓reduceIte, ↓reduceDIte, post, hostStep, Step.map]; exact trel_bad
  have hv₁ := Classical.not_not.1 hnv
  have hnw₁ : mem₁.cumAlloced.toNat + size.toNat < Word.size := by
    by_cases hp : 0 < size.toNat
    · obtain ⟨a, ha⟩ := hv₁
      have := no_wrap i₁ ha hp
      simp only [CompilerReservedBytes] at this
      omega
    · have := mem₁.cumAlloced.toNat_lt
      simp only [Word.size, Word.bits]; omega
  have hn₁ : mem₁.cumAlloced.toNat + size.toNat < 2 ^ 64 := by
    have := mt (check_iff hnw₁).2 hck₁; omega
  have hck₂ : ¬((mem₂.cumAlloced.toNat : Word) + size ≥ (UInt64.size : Word)) := by
    have := hc.cum
    rw [check_iff (by omega)]; omega
  have hv₂ : ∃ a', mem₂.ValidAlloc size.toNat a' := let ⟨a, ha⟩ := hv₁; ⟨a, valid_of_corr hc ha⟩
  simp only [hck₁, hck₂, hv₁, hv₂, ↓reduceIte, ↓reduceDIte, post, hostStep, Step.map]
  refine trel_branch fun ⟨a₂, ha₂⟩ hsub => ?_
  have hd : 0 < size.toNat → ∀ r ∈ mem₁.taken, r.Disjoint a₂.range := by
    intro hp r hr
    have hin : a₂.range ∈ L := by
      have hp' : size > 0 := by simpa [BitVec.lt_def] using hp
      cases kind <;> simp only [Function.comp_apply, hp', ↓reduceIte, taken_push] at hsub <;>
        first
        | exact zeroed_range a₂ ▸ hsub _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
        | exact hsub _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ha₂.2.2 hp _ (hc.reserved ▸ List.mem_cons_self)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hr
      rcases corr_live hc hb with hb | hb
      · exact ha₂.2.2 hp _ (mem_taken_of_live hb)
      · exact disjoint_symm (hb _ hin)
  refine ⟨⟨a₂, ha₂.1, ha₂.2.1, hd⟩, ?_⟩
  cases kind
  · refine corr_alloc hc i₁ i₂ (by rw [zeroed_size]; exact ha₂.1)
      (by simp only [Allocation.end]; rw [zeroed_size]; exact ha₂.2.1)
      (by rw [zeroed_range]; exact hd) (by rw [zeroed_range]; exact ha₂.2.2) hn₁ (hk _)
  · exact corr_alloc hc i₁ i₂ ha₂.1 ha₂.2.1 hd ha₂.2.2 hn₁ (hk _)

lemma match_step (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (i₂ : MemInv mem₂) {m₁ m₂ : SirM Empty}
    (hs' : StepRel (OpRel.eq EvalE) Eq (Skip DeadExtra (fun _ => False) Eq) m₁.observe m₂.observe) :
    TRel L (Sub (faultPts m₂.observe) L) (tstep self (hs, mem₁, m₁)) (tstep self (hs, mem₂, m₂)) := by
  generalize he₁ : m₁.observe = s₁ at hs'
  generalize he₂ : m₂.observe = s₂ at hs'
  rcases s₁ with a | n₁ | ⟨o₁, k₁⟩ | ⟨c, _⟩ <;> rcases s₂ with b | n₂ | ⟨o₂, k₂⟩ | ⟨c', _⟩ <;>
    simp only [StepRel, OpRel.eq] at hs'
  · exact nomatch a
  · rw [tstep_silent self he₁, tstep_silent self he₂]
    exact trel_silent ⟨rfl, hc, i₁, i₂, hs'⟩
  · obtain ⟨rfl, hk⟩ := hs'
    have hk' : ∀ r, Skip DeadExtra (fun _ => False) Eq (k₁ r) (k₂ r) := fun r => hk r r HEq.rfl
    rw [tstep_post self he₁, tstep_post self he₂]
    rcases o₁ with op | op
    · exact match_host hc i₁ i₂ op hk'
    · cases op with
      | alloc kind size => exact match_alloc hc i₁ i₂ kind size hk'
      | read o len => exact match_read hc i₁ i₂ o len hk'
      | write o bytes => exact match_write hc i₁ i₂ o bytes hk'
      | copy c =>
        obtain ⟨dst, src, len⟩ := c
        exact match_copy hc i₁ i₂ dst src len hk'
      | ub u => exact match_ub u
  · exact nomatch c

def ENext (L : List NatRange) (mem₂ : MemState) (hs : HostState) {R : Type} (k : R → SirM Empty)
    (q : Triple) : Prop :=
  q.1 = hs ∧ (∃ r, q.2.2 = k r) ∧ MemCorr L q.2.1 mem₂ ∧ MemInv q.2.1

def EStep (L : List NatRange) (mem₂ : MemState) (hs : HostState) {R : Type} (k : R → SirM Empty)
    (s : Step WorldE MemoryND (UB ⊕ Outcome) Triple) : Prop :=
  (∃ u, s = .pure (.inl u)) ∨ (∃ q, s = .silent q ∧ ENext L mem₂ hs k q) ∨
    ∃ c kk r, s = .branch c kk ∧ ENext L mem₂ hs k (kk r)

lemma extra_alloc (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (hL : Small L) (kind : AllocKind)
    (size : Word) {k : Word → SirM Empty} :
    EStep L mem₂ hs k (post self hs k (memStep mem₁ (.impure (.inr (.alloc kind size)) id))) := by
  simp only [memStep]
  by_cases hck₁ : (mem₁.cumAlloced.toNat : Word) + size ≥ (UInt64.size : Word)
  · simp only [hck₁, ↓reduceIte, post, hostStep, Step.map]; exact .inl ⟨_, rfl⟩
  by_cases hnv : ¬∃ a', mem₁.ValidAlloc size.toNat a'
  · simp only [hck₁, hnv, ↓reduceIte, ↓reduceDIte, post, hostStep, Step.map]; exact .inl ⟨_, rfl⟩
  have hv₁ := Classical.not_not.1 hnv
  simp only [hck₁, hv₁, ↓reduceIte, ↓reduceDIte, post, hostStep, Step.map]
  refine .inr (.inr ?_)
  by_cases hp : 0 < size.toNat
  · have hnw₁ : mem₁.cumAlloced.toNat + size.toNat < Word.size := by
      obtain ⟨a, ha⟩ := hv₁
      have := no_wrap i₁ ha hp
      simp only [CompilerReservedBytes] at this
      omega
    have hn₁ : mem₁.cumAlloced.toNat + size.toNat < 2 ^ 64 := by
      have := mt (check_iff hnw₁).2 hck₁; omega
    obtain ⟨st, hst, hdis⟩ := exists_fresh (L ++ mem₁.taken) size.toNat
      (by have := hL.1; have := i₁.count; rw [List.length_append]; omega)
      (fun r hr => by
        rcases List.mem_append.1 hr with hr | hr
        · have := hL.2 r hr; omega
        · have := i₁.small r hr; omega)
      (by omega)
    have hst' : (Word.ofNat st).toNat = st := Nat.mod_eq_of_lt (by simp only [Word.size] at hst; omega)
    let a' : Allocation := ⟨Word.ofNat st, ⟨.replicate size.toNat 0⟩⟩
    have hsz : a'.size = size.toNat := by simp only [a', Allocation.size, ByteArray.size, Array.size_replicate]
    have hrange : a'.range = ⟨st, size.toNat⟩ := by simp only [Allocation.range, hsz, a', hst']
    have hva : mem₁.ValidAlloc size.toNat a' :=
      ⟨hsz, by simp only [Allocation.end, hsz, a', hst']; exact hst,
        fun _ r hr => hrange ▸ hdis r (List.mem_append_right _ hr)⟩
    have hp' : size > 0 := by simpa [BitVec.lt_def] using hp
    have hav : ∀ A : Allocation, A.range = a'.range → Avoids L A := fun A hA r hr =>
      hA ▸ hrange ▸ hdis r (List.mem_append_left _ hr)
    have hvd : ∀ A : Allocation, A.range = a'.range → ∀ r ∈ mem₁.taken, r.Disjoint A.range :=
      fun A hA r hr => hA ▸ hva.2.2 hp r hr
    refine ⟨.alloc size mem₁ hv₁, _, (⟨a', hva⟩ : {a' // mem₁.ValidAlloc size.toNat a'}), rfl, rfl, ⟨_, rfl⟩, ?_⟩
    cases kind
    · simp only [hp', ↓reduceIte]
      have hzs := zeroed_size a'
      have hzr := zeroed_range a'
      exact ⟨corr_push_dead hc _ (by rw [hzs, hsz]; omega) (hav _ hzr),
        inv_push i₁ (hvd _ hzr) (by rw [hzs, hsz]; omega) (by rw [hzs, hsz]; omega)
          (by simp only [Allocation.end]; rw [hzs]; exact hva.2.1)⟩
    · simp only [hp', ↓reduceIte]
      exact ⟨corr_push_dead hc a' (by rw [hsz]; omega) (hav _ rfl),
        inv_push i₁ (hvd _ rfl) (by rw [hsz]; omega) (by rw [hsz]; omega) hva.2.1⟩
  · obtain ⟨a, ha⟩ := hv₁
    have hp' : ¬size > 0 := by simpa [BitVec.lt_def] using hp
    refine ⟨.alloc size mem₁ ⟨a, ha⟩, _, (⟨a, ha⟩ : {a' // mem₁.ValidAlloc size.toNat a'}), rfl, rfl, ⟨_, rfl⟩, ?_⟩
    cases kind <;> simp only [hp', ↓reduceIte] <;> exact ⟨hc, i₁⟩

lemma extra_step (hc : MemCorr L mem₁ mem₂) (i₁ : MemInv mem₁) (hL : Small L) {op : EvalE.Op}
    (hx : DeadExtra op) {k : EvalE.Resp op → SirM Empty} :
    EStep L mem₂ hs k (post self hs k (memStep mem₁ (.impure op id))) := by
  rcases op with op | op
  · cases op <;> simp only [DeadExtra, HostRead] at hx <;>
      exact .inr (.inl ⟨_, rfl, rfl, ⟨_, rfl⟩, hc, i₁⟩)
  · cases op with
    | alloc kind size => exact extra_alloc hc i₁ hL kind size
    | read o len =>
      simp only [memStep]
      by_cases h0 : len = 0
      · simp only [h0, ↓reduceIte, post, hostStep, Step.map]
        exact .inr (.inl ⟨_, rfl, rfl, ⟨_, rfl⟩, hc, i₁⟩)
      · simp only [h0, ↓reduceIte]
        cases mem₁.inBounds o len.toNat with
        | none => exact .inl ⟨_, rfl⟩
        | some r => exact .inr (.inl ⟨_, rfl, rfl, ⟨_, rfl⟩, hc, i₁⟩)
    | ub u => exact .inl ⟨_, rfl⟩
    | write => exact hx.elim
    | copy => exact hx.elim

end Steps

section Succ

variable {self : Address}

def Succ {E : Effect} {N : NonDeterminism} {A : Type} {S : Type 1} : Step E N A S → S → Prop
  | .pure _, _ => False
  | .silent x, y => x = y
  | .impure _ k, y => ∃ r, k r = y
  | .branch _ k, y => ∃ r, k r = y

def Succ₀ {E : Effect} {N : NonDeterminism} {A : Type} {S : Type} : Step E N A S → S → Prop
  | .pure _, _ => False
  | .silent x, y => x = y
  | .impure _ k, y => ∃ r, k r = y
  | .branch _ k, y => ∃ r, k r = y

lemma succ_map {E : Effect} {N : NonDeterminism} {A : Type} {S : Type} {T : Type 1}
    (s : Step E N A S) (f : S → T) (y : T) (h : Succ (s.map f) y) : ∃ x, Succ₀ s x ∧ f x = y := by
  rcases s with a | x | ⟨op, k⟩ | ⟨c, k⟩
  · exact h.elim
  · exact ⟨x, rfl, h⟩
  · obtain ⟨r, hr⟩ := h; exact ⟨k r, ⟨r, rfl⟩, hr⟩
  · obtain ⟨r, hr⟩ := h; exact ⟨k r, ⟨r, rfl⟩, hr⟩

lemma succ_hostStep {N : NonDeterminism} {A X : Type} (hs : HostState) (s : Step HostE N A X)
    (p : HostState × X) (h : Succ₀ (hostStep self hs s) p) : Succ₀ s p.2 := by
  rcases s with a | x | ⟨op, k⟩ | ⟨c, k⟩
  · exact h.elim
  · cases h; rfl
  · rw [show (Step.impure op k : Step HostE N A X) = (Step.impure op id).map k from rfl,
      DeadCode.hostStep_nat] at h
    rcases hh : hostStep self hs (Step.impure op id : Step HostE N A (HostE.Resp op)) with
      a | y | ⟨op', k'⟩ | ⟨c, k'⟩ <;> rw [hh] at h
    · exact h.elim
    · cases h; exact ⟨_, rfl⟩
    · obtain ⟨r, rfl⟩ := h; exact ⟨_, rfl⟩
    · obtain ⟨r, rfl⟩ := h; exact ⟨_, rfl⟩
  · obtain ⟨r, rfl⟩ := h; exact ⟨r, rfl⟩

structure MemOK (m m' : MemState) : Prop where
  inv : MemInv m'
  sub : Sub m.taken m'.taken
  cum : m.cumAlloced.toNat ≤ m'.cumAlloced.toNat
  stable : m'.cumAlloced.toNat ≤ m.cumAlloced.toNat → m'.taken = m.taken

lemma ok_refl {m : MemState} (hI : MemInv m) : MemOK m m :=
  ⟨hI, fun _ h => h, Nat.le_refl _, fun _ => rfl⟩

lemma ok_write {m : MemState} (hI : MemInv m) {o : Word} {len : Nat} (bytes : ByteArray)
    (r : m.Region o len) : MemOK m (m.write bytes r) :=
  ⟨inv_write hI bytes r, by rw [taken_write]; exact fun _ h => h, Nat.le_refl _,
    fun _ => taken_write m bytes r⟩

lemma ok_push {m : MemState} {a : Allocation} (hI : MemInv m) (hv : ∀ r ∈ m.taken, r.Disjoint a.range)
    (hpos : 0 < a.size) (hcum : m.cumAlloced.toNat + a.size < 2 ^ 64) (hend : a.end ≤ Word.size) :
    MemOK m (m.push a) :=
  ⟨inv_push hI hv hpos hcum hend, by rw [taken_push]; exact fun _ h => List.mem_append_left _ h,
    by rw [cum_push _ _ hcum]; omega, fun h => by rw [cum_push _ _ hcum] at h; omega⟩

lemma memStep_succ {mem : MemState} (hI : MemInv mem) {op : EvalE.Op}
    (p : MemState × EvalE.Resp op) (h : Succ₀ (memStep mem (.impure op id)) p) : MemOK mem p.1 := by
  rcases op with op | op
  · obtain ⟨r, rfl⟩ := h; exact ok_refl hI
  · cases op with
    | ub u => exact h.elim
    | read o len =>
      simp only [memStep] at h
      split at h
      · cases h; exact ok_refl hI
      · split at h
        · cases h; exact ok_refl hI
        · exact h.elim
    | write o bytes =>
      simp only [memStep] at h
      split at h
      · cases h; exact ok_refl hI
      · split at h
        · cases h; exact ok_write hI _ _
        · exact h.elim
    | copy c =>
      obtain ⟨dst, src, len⟩ := c
      simp only [memStep] at h
      split at h
      · cases h; exact ok_refl hI
      · split at h
        · cases h; exact ok_write hI _ _
        · exact h.elim
        · exact h.elim
    | alloc kind size =>
      simp only [memStep] at h
      by_cases hck : (mem.cumAlloced.toNat : Word) + size ≥ (UInt64.size : Word)
      · simp only [hck, ↓reduceIte] at h; exact h.elim
      by_cases hnv : ¬∃ a', mem.ValidAlloc size.toNat a'
      · simp only [hck, hnv, ↓reduceIte, ↓reduceDIte] at h; exact h.elim
      have hv := Classical.not_not.1 hnv
      simp only [hck, hv, ↓reduceIte, ↓reduceDIte] at h
      obtain ⟨⟨a, ha⟩, rfl⟩ := h
      by_cases hp : 0 < size.toNat
      · have hnw : mem.cumAlloced.toNat + size.toNat < Word.size := by
          have := no_wrap hI ha hp
          simp only [CompilerReservedBytes] at this
          omega
        have hn : mem.cumAlloced.toNat + size.toNat < 2 ^ 64 := by
          have := mt (check_iff hnw).2 hck; omega
        have hp' : size > 0 := by simpa [BitVec.lt_def] using hp
        cases kind
        · simp only [hp', ↓reduceIte]
          exact ok_push hI (fun r hr => zeroed_range a ▸ ha.2.2 hp r hr) (by rw [zeroed_size, ha.1]; omega)
            (by rw [zeroed_size, ha.1]; omega) (by simp only [Allocation.end]; rw [zeroed_size]; exact ha.2.1)
        · simp only [hp', ↓reduceIte]
          exact ok_push hI (ha.2.2 hp) (by rw [ha.1]; omega) (by rw [ha.1]; omega) ha.2.1
      · have hp' : ¬size > 0 := by simpa [BitVec.lt_def] using hp
        cases kind <;> simp only [hp', ↓reduceIte] <;> exact ok_refl hI

lemma tstep_succ {q q' : Triple} (hI : MemInv q.2.1) (h : Succ (tstep self q) q') : MemOK q.2.1 q'.2.1 := by
  obtain ⟨hs, mem, m⟩ := q
  rcases observe_cases m with ⟨n, hn⟩ | ⟨op, k, hk⟩
  · rw [tstep_silent self hn] at h
    cases h
    exact ok_refl hI
  · rw [tstep_post self hk] at h
    obtain ⟨p, hp, rfl⟩ := succ_map _ _ _ h
    exact memStep_succ hI p.2 (succ_hostStep hs _ p hp)

end Succ

section Transfer

variable {self : Address} {β : Type} {F : UB ⊕ Outcome → β} {bad : β → Prop}

def TStep (self : Address) (q q' : Triple) : Prop :=
  tstep self q = .silent q' ∨ ∃ c k r, tstep self q = .branch c k ∧ k r = q'

lemma TStep.succ {q q' : Triple} (h : TStep self q q') : Succ (tstep self q) q' := by
  rcases h with h | ⟨c, k, r, h, rfl⟩ <;> rw [h]
  · rfl
  · exact ⟨r, rfl⟩

lemma W_obs_pure {q : Triple} {a : UB ⊕ Outcome} (h : tstep self q = .pure a) :
    (W self F q).observe = .pure (F a) := by rw [W_observe, h]; rfl

lemma W_obs_silent {q q' : Triple} (h : tstep self q = .silent q') :
    (W self F q).observe = .silent (W self F q') := by rw [W_observe, h]; rfl

lemma W_obs_impure {q : Triple} {op : WorldE.Op} {k : WorldE.Resp op → Triple}
    (h : tstep self q = .impure op k) : (W self F q).observe = .impure op fun r => W self F (k r) := by
  rw [W_observe, h]; rfl

lemma W_obs_branch {q : Triple} {c : MemoryND.Op} {k : MemoryND.Resp c → Triple}
    (h : tstep self q = .branch c k) : (W self F q).observe = .branch c fun r => W self F (k r) := by
  rw [W_observe, h]; rfl

lemma W_pure_inv {q : Triple} {b : β} (h : (W self F q).observe = .pure b) :
    ∃ a, tstep self q = .pure a ∧ F a = b := by
  rw [W_observe] at h
  generalize tstep self q = s at h
  rcases s <;> simp only [liftStep, Step.pure.injEq, reduceCtorEq] at h
  exact ⟨_, rfl, h⟩

lemma W_impure_inv {q : Triple} {op : WorldE.Op} {k : WorldE.Resp op → CoFree WorldE MemoryND β}
    (h : (W self F q).observe = .impure op k) :
    ∃ k', tstep self q = .impure op k' ∧ ∀ r, k r = W self F (k' r) := by
  rw [W_observe] at h
  generalize tstep self q = s at h
  rcases s <;> simp only [liftStep, Step.impure.injEq, reduceCtorEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  exact ⟨_, rfl, fun _ => rfl⟩

lemma W_ustep_inv {q : Triple} {z' : CoFree WorldE MemoryND β} (h : UStep (W self F q) z') :
    ∃ q', TStep self q q' ∧ z' = W self F q' := by
  rw [UStep, W_observe] at h
  generalize hs : tstep self q = s at h
  rcases h with h | ⟨c, k, r, h, rfl⟩ <;> rcases s <;>
    simp only [liftStep, Step.silent.injEq, Step.branch.injEq, reduceCtorEq] at h
  · exact ⟨_, .inl hs, h.symm⟩
  · obtain ⟨rfl, h⟩ := h
    cases h
    exact ⟨_, .inr ⟨_, _, r, hs, rfl⟩, rfl⟩

lemma nobad_contra {q : Triple} {u : UB} (hF : ∀ u, bad (F (.inl u))) (hnb : NoBad bad (W self F q))
    (h : tstep self q = .pure (.inl u)) : False :=
  hnb _ (hF u) (.res (W_obs_pure h))

lemma small_L₀ {q : Triple} (hI : MemInv q.2.1) : Small (q.2.1.taken ++ faultPts q.2.2.observe) := by
  have hf : (faultPts q.2.2.observe).length ≤ 2 ∧ ∀ r ∈ faultPts q.2.2.observe, r.size ≤ 1 := by
    unfold faultPts
    split <;> simp
  refine ⟨?_, fun r hr => ?_⟩
  · have := hI.count
    have := q.2.1.cumAlloced.toNat_lt
    rw [List.length_append]
    omega
  · rcases List.mem_append.1 hr with hr | hr
    · exact hI.small r hr
    · have := hf.2 r hr; omega

lemma sub_trans {L₁ L₂ L₃ : List NatRange} (h₁ : Sub L₁ L₂) (h₂ : Sub L₂ L₃) : Sub L₁ L₃ :=
  fun r hr => h₂ r (h₁ r hr)

variable {N' : NonDeterminism} {α : Type} {Ret : α → β → Prop} {x : CoFree WorldE N' α}

lemma peel (hF : ∀ u, bad (F (.inl u))) {L : List NatRange} (hL : Small L) (q₂ : Triple)
    (hP : ∀ q₁, Corr L q₁ q₂ →
      StepRel (OpRel.eq EvalE) Eq (Skip DeadExtra (fun _ => False) Eq) q₁.2.2.observe q₂.2.2.observe →
      NoBad bad (W self F q₁) → ¬Same Ret x (W self F q₁)) :
    ∀ q₁, Corr L q₁ q₂ → NoBad bad (W self F q₁) → ¬Same Ret x (W self F q₁) := by
  obtain ⟨hs, mem₂, m₂⟩ := q₂
  rintro ⟨hs₁, mem₁, m₁⟩ ⟨hh, hcm, i₁, i₂, hsk⟩
  dsimp only at hh hcm i₁ i₂ hsk
  subst hh
  have hf := CoFree.Proofs.Skip.unfold hsk
  clear hsk
  induction hf generalizing mem₁ with
  | step hst => exact hP _ ⟨rfl, hcm, i₁, i₂, CoFree.Proofs.Skip.fold (.step hst)⟩ hst
  | silentL h₁ _ ih =>
    intro hnb hsame
    have ho := W_obs_silent (F := F) (tstep_silent self (hs := hs₁) (mem := mem₁) h₁)
    exact ih mem₁ hcm i₁ hP (CoFree.Proofs.noBad_silent hnb ho) (Same.silentR_inv hsame ho)
  | extraL op h₁ hx _ ih =>
    intro hnb hsame
    have e := tstep_post self (hs := hs₁) (mem := mem₁) h₁
    rcases extra_step (self := self) (hs := hs₁) hcm i₁ hL hx with ⟨u, hu⟩ | ⟨q, hq, hn⟩ | ⟨c, kk, r, hq, hn⟩
    · exact nobad_contra hF hnb (e.trans hu)
    · obtain ⟨qh, ⟨r, hr⟩, hcm', i₁'⟩ := hn
      obtain ⟨qh', qm', qs'⟩ := q
      dsimp only at qh hr hcm' i₁'
      subst qh hr
      have ho := W_obs_silent (F := F) (e.trans hq)
      exact ih r qm' hcm' i₁' hP (CoFree.Proofs.noBad_silent hnb ho) (Same.silentR_inv hsame ho)
    · obtain ⟨qh, ⟨r', hr⟩, hcm', i₁'⟩ := hn
      have ho := W_obs_branch (F := F) (e.trans hq)
      have hnb' := CoFree.Proofs.noBad_branch hnb ho r
      have hs' := Same.branchR_inv hsame ho r
      generalize kk r = q at qh hr hcm' i₁' hnb' hs'
      obtain ⟨qh', qm', qs'⟩ := q
      dsimp only at qh hr hcm' i₁'
      subst qh hr
      exact ih r' qm' hcm' i₁' hP hnb' hs'
  | badL _ _ hb => exact hb.elim

lemma ystep {L : List NatRange} (hL : Small L) {q₁ q₂ : Triple} (hc : Corr L q₁ q₂) :
    (∃ q₁', tstep self q₁ = .silent q₁' ∧ Corr L q₁' q₂) ∨
    (∃ c kk r, tstep self q₁ = .branch c kk ∧ Corr L (kk r) q₂) ∨
    TRel L (Sub (faultPts q₂.2.2.observe) L) (tstep self q₁) (tstep self q₂) := by
  obtain ⟨hs, mem₂, m₂⟩ := q₂
  obtain ⟨hs₁, mem₁, m₁⟩ := q₁
  obtain ⟨hh, hcm, i₁, i₂, hsk⟩ := hc
  dsimp only at hh hcm i₁ i₂ hsk
  subst hh
  cases CoFree.Proofs.Skip.unfold hsk with
  | step hst => exact .inr (.inr (match_step hcm i₁ i₂ hst))
  | silentL h₁ hf => exact .inl ⟨_, tstep_silent self h₁, rfl, hcm, i₁, i₂, CoFree.Proofs.Skip.fold hf⟩
  | extraL op h₁ hx hk =>
    rw [tstep_post self h₁]
    rcases extra_step (self := self) (hs := hs₁) hcm i₁ hL hx with ⟨u, hu⟩ | ⟨q, hq, hn⟩ | ⟨c, kk, r, hq, hn⟩
    · exact .inr (.inr (.inl ⟨u, hu⟩))
    · obtain ⟨qh, ⟨r, hr⟩, hcm', i₁'⟩ := hn
      refine .inl ⟨q, hq, qh, hcm', i₁', i₂, ?_⟩
      rw [hr]; exact CoFree.Proofs.Skip.fold (hk r)
    · obtain ⟨qh, ⟨r', hr⟩, hcm', i₁'⟩ := hn
      refine .inr (.inl ⟨c, kk, r, hq, qh, hcm', i₁', i₂, ?_⟩)
      rw [hr]; exact CoFree.Proofs.Skip.fold (hk r')
  | badL _ _ hb => exact hb.elim

def SameShape (y z : CoFree WorldE MemoryND β) : Prop :=
  (∃ b, y.observe = .pure b ∧ z.observe = .pure b) ∨
  ∃ op k₁ k₂, y.observe = .impure op k₁ ∧ z.observe = .impure op k₂

lemma matched_visible (hF : ∀ u, bad (F (.inl u))) {L : List NatRange} {cov : Prop} {q₁ q₂ : Triple}
    (ht : TRel L cov (tstep self q₁) (tstep self q₂)) (hcov : cov) (hnb : NoBad bad (W self F q₁))
    (hz : Visible (W self F q₂)) : SameShape (W self F q₁) (W self F q₂) := by
  rcases ht with ⟨u, hu⟩ | ht
  · exact (nobad_contra hF hnb hu).elim
  rcases CoFree.Proofs.visible_cases hz with ⟨b, hb⟩ | ⟨op, k, hk⟩
  · obtain ⟨a, ha, rfl⟩ := W_pure_inv hb
    rw [ha] at ht
    exact .inl ⟨F a, W_obs_pure (ht hcov), hb⟩
  · obtain ⟨k', hk', -⟩ := W_impure_inv hk
    rw [hk'] at ht
    obtain ⟨k₁, h₁, -⟩ := ht
    exact .inr ⟨op, _, _, W_obs_impure h₁, hk⟩

lemma shape_visible {y z : CoFree WorldE MemoryND β} (h : SameShape y z) : Visible y := by
  rcases h with ⟨b, hy, -⟩ | ⟨op, k₁, k₂, hy, -⟩
  · exact CoFree.Proofs.visible_pure hy
  · exact CoFree.Proofs.visible_impure hy

lemma shape_visMatch {y z : CoFree WorldE MemoryND β} (h : SameShape y z) (hm : VisMatch x y) :
    VisMatch x z := by
  rcases h with ⟨b, hy, hz⟩ | ⟨op, k₁, k₂, hy, hz⟩ <;>
    rcases hm with ⟨a, b', hx, hy'⟩ | ⟨op', k, k', hx, hy'⟩ <;> rw [hy] at hy' <;> cases hy'
  · exact .inl ⟨a, b, hx, hz⟩
  · exact .inr ⟨op, k, k₂, hx, hz⟩

lemma match_step' {L : List NatRange} {q₁ q₂ : Triple} (hc : Corr L q₁ q₂)
    (hst : StepRel (OpRel.eq EvalE) Eq (Skip DeadExtra (fun _ => False) Eq) q₁.2.2.observe q₂.2.2.observe) :
    TRel L (Sub (faultPts q₂.2.2.observe) L) (tstep self q₁) (tstep self q₂) := by
  obtain ⟨hs, mem₂, m₂⟩ := q₂
  obtain ⟨hs₁, mem₁, m₁⟩ := q₁
  obtain ⟨hh, hcm, i₁, i₂, -⟩ := hc
  dsimp only at hh hcm i₁ i₂ hst
  subst hh
  exact match_step hcm i₁ i₂ hst

lemma stabilize (c : Nat → Nat) (hmono : ∀ n, c n ≤ c (n + 1)) (B : Nat) (hb : ∀ n, c n < B) :
    ∃ N, ∀ n, N ≤ n → c n = c N := by
  have hle : ∀ n m, n ≤ m → c n ≤ c m := fun n m h => by
    induction h with
    | refl => exact Nat.le_refl _
    | step _ ih => exact Nat.le_trans ih (hmono _)
  refine Classical.byContradiction fun h => ?_
  have hgrow : ∀ k, ∃ N, k ≤ c N := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      have : ∃ n, N ≤ n ∧ c n ≠ c N := Classical.byContradiction fun hn =>
        h ⟨N, fun n hn' => Classical.byContradiction fun hne => hn ⟨n, hn', hne⟩⟩
      obtain ⟨n, hn, hne⟩ := this
      have := hle N n hn
      exact ⟨n, by omega⟩
  obtain ⟨N, hN⟩ := hgrow B
  have := hb N
  omega

lemma advance (hF : ∀ u, bad (F (.inl u))) {L : List NatRange} (hL : Small L) {q₁ q₂ q₂' : Triple}
    (hc : Corr L q₁ q₂) (hnb : NoBad bad (W self F q₁)) (hts : TStep self q₂ q₂')
    (hsub : Sub q₂'.2.1.taken L) :
    (∃ q₁', tstep self q₁ = .silent q₁' ∧ (Corr L q₁' q₂ ∨ Corr L q₁' q₂')) ∨
    (∃ c kk r, tstep self q₁ = .branch c kk ∧ (Corr L (kk r) q₂ ∨ Corr L (kk r) q₂')) := by
  rcases ystep hL hc with ⟨q₁', h, hc'⟩ | ⟨c, kk, r, h, hc'⟩ | ht
  · exact .inl ⟨q₁', h, .inl hc'⟩
  · exact .inr ⟨c, kk, r, h, .inl hc'⟩
  rcases ht with ⟨u, hu⟩ | ht
  · exact (nobad_contra hF hnb hu).elim
  rcases hts with h | ⟨c, k, r, h, rfl⟩ <;> rw [h] at ht
  · obtain ⟨q₁', h₁, hc'⟩ := ht
    exact .inl ⟨q₁', h₁, .inr hc'⟩
  · obtain ⟨c', k₁, h₁, hall⟩ := ht
    obtain ⟨r₁, hc'⟩ := hall r hsub
    exact .inr ⟨c', k₁, r₁, h₁, .inr hc'⟩

lemma divR_case (hF : ∀ u, bad (F (.inl u))) (hx : Visible x) (f : Nat → CoFree WorldE MemoryND β)
    (hc : Chain f) (q₂ : Triple) (h0 : f 0 = W self F q₂) (hI : MemInv q₂.2.1) :
    ∃ L, Small L ∧ Sub q₂.2.1.taken L ∧
      ∀ q₁, Corr L q₁ q₂ → NoBad bad (W self F q₁) → ¬Same Ret x (W self F q₁) := by
  have step : ∀ n (q : Triple), f n = W self F q → MemInv q.2.1 →
      ∃ q', TStep self q q' ∧ f (n + 1) = W self F q' ∧ MemInv q'.2.1 := by
    intro n q hq hI'
    have := hc n
    rw [hq] at this
    obtain ⟨q', ht, he⟩ := W_ustep_inv this
    exact ⟨q', ht, he, (tstep_succ hI' ht.succ).inv⟩
  let g : (n : Nat) → {q : Triple // f n = W self F q ∧ MemInv q.2.1} := fun n =>
    Nat.rec (motive := fun n => {q : Triple // f n = W self F q ∧ MemInv q.2.1}) ⟨q₂, h0, hI⟩
      (fun n p => ⟨Classical.choose (step n p.1 p.2.1 p.2.2),
        (Classical.choose_spec (step n p.1 p.2.1 p.2.2)).2⟩) n
  have hg : ∀ n, TStep self (g n).1 (g (n + 1)).1 := fun n =>
    (Classical.choose_spec (step n (g n).1 (g n).2.1 (g n).2.2)).1
  have hok : ∀ n, MemOK (g n).1.2.1 (g (n + 1)).1.2.1 := fun n => tstep_succ (g n).2.2 (hg n).succ
  obtain ⟨N, hN⟩ := stabilize (fun n => (g n).1.2.1.cumAlloced.toNat) (fun n => (hok n).cum) (2 ^ 64)
    (fun n => UInt64.toNat_lt _)
  have hmono : ∀ n m, n ≤ m → Sub (g n).1.2.1.taken (g m).1.2.1.taken := fun n m h => by
    induction h with
    | refl => exact fun _ h => h
    | step _ ih => exact sub_trans ih (hok _).sub
  have hstable' : ∀ d, (g (N + d)).1.2.1.taken = (g N).1.2.1.taken := fun d => by
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [← ih]
      refine (hok (N + d)).stable ?_
      have h₁ := hN (N + d) (by omega)
      have h₂ := hN (N + d + 1) (by omega)
      omega
  have hstable : ∀ n, N ≤ n → (g n).1.2.1.taken = (g N).1.2.1.taken := fun n h => by
    have := hstable' (n - N)
    rwa [Nat.add_sub_cancel' h] at this
  have hsubL : ∀ n, Sub (g n).1.2.1.taken (g N).1.2.1.taken := fun n => by
    rcases Nat.le_total n N with h | h
    · exact hmono n N h
    · rw [hstable n h]; exact fun _ h => h
  have hIN := (g N).2.2
  have hsmall : Small (g N).1.2.1.taken := by
    refine ⟨?_, hIN.small⟩
    have := hIN.count
    have := (g N).1.2.1.cumAlloced.toNat_lt
    omega
  refine ⟨_, hsmall, hmono 0 N (Nat.zero_le _), fun q₁ hcq hnb hsame => ?_⟩
  have key : ∀ (x' : CoFree WorldE N' α) (y : CoFree WorldE MemoryND β), SameFinite Ret (Same Ret) x' y →
      Visible x' → ∀ n q₁, y = W self F q₁ → Corr (g N).1.2.1.taken q₁ (g n).1 →
        NoBad bad (W self F q₁) → False := by
    intro x' y hsf
    induction hsf with
    | ret a b _ hy _ =>
      intro _ n q₁ hq hc' hnb'
      subst hq
      rcases advance hF hsmall hc' hnb' (hg n) (hsubL _) with ⟨q₁', h, -⟩ | ⟨c, kk, r, h, -⟩
      · rw [W_obs_silent h] at hy; cases hy
      · rw [W_obs_branch h] at hy; cases hy
    | impure op _ hy _ =>
      intro _ n q₁ hq hc' hnb'
      subst hq
      rcases advance hF hsmall hc' hnb' (hg n) (hsubL _) with ⟨q₁', h, -⟩ | ⟨c, kk, r, h, -⟩
      · rw [W_obs_silent h] at hy; cases hy
      · rw [W_obs_branch h] at hy; cases hy
    | silentL hx' => intro hv; exact (hv ((forallUnobserved_silent hx').2 trivial)).elim
    | branchL c hx' => intro hv; exact (hv ((forallUnobserved_branch hx').2 fun _ => trivial)).elim
    | mutualUnobservedStep hu =>
      intro hv
      exact (hv (forallUnobserved_mono hu fun _ _ => trivial)).elim
    | silentR hy _ ih =>
      intro hv n q₁ hq hc' hnb'
      subst hq
      rcases advance hF hsmall hc' hnb' (hg n) (hsubL _) with ⟨q₁', h, hc''⟩ | ⟨c, kk, r, h, -⟩
      · have ho := W_obs_silent (F := F) h
        rw [ho] at hy
        cases hy
        rcases hc'' with hc'' | hc''
        · exact ih hv n q₁' rfl hc'' (CoFree.Proofs.noBad_silent hnb' ho)
        · exact ih hv (n + 1) q₁' rfl hc'' (CoFree.Proofs.noBad_silent hnb' ho)
      · rw [W_obs_branch h] at hy; cases hy
    | branchR c hy _ ih =>
      intro hv n q₁ hq hc' hnb'
      subst hq
      rcases advance hF hsmall hc' hnb' (hg n) (hsubL _) with ⟨q₁', h, -⟩ | ⟨c', kk, r, h, hc''⟩
      · rw [W_obs_silent h] at hy; cases hy
      · have ho := W_obs_branch (F := F) h
        rw [ho] at hy
        cases hy
        rcases hc'' with hc'' | hc''
        · exact ih r hv n (kk r) rfl hc'' (CoFree.Proofs.noBad_branch hnb' ho r)
        · exact ih r hv (n + 1) (kk r) rfl hc'' (CoFree.Proofs.noBad_branch hnb' ho r)
  exact key x _ (Same.unfold hsame) hx 0 q₁ rfl hcq hnb

lemma base_case (hF : ∀ u, bad (F (.inl u))) (q₂ : Triple) (hI : MemInv q₂.2.1)
    (hvis : Visible (W self F q₂))
    (concl : ∀ y : CoFree WorldE MemoryND β, SameShape y (W self F q₂) → ¬Same Ret x y) :
    ∃ L, Small L ∧ Sub q₂.2.1.taken L ∧
      ∀ q₁, Corr L q₁ q₂ → NoBad bad (W self F q₁) → ¬Same Ret x (W self F q₁) :=
  ⟨_, small_L₀ hI, fun _ hr => List.mem_append_left _ hr, peel hF (small_L₀ hI) q₂ fun _ hc hst hnb =>
    concl _ (matched_visible hF (match_step' hc hst) (fun _ hr => List.mem_append_right _ hr) hnb hvis)⟩

lemma transfer (hF : ∀ u, bad (F (.inl u))) {x : CoFree WorldE N' α} {z : CoFree WorldE MemoryND β}
    (hb : Bad Ret x z) : ∀ q₂, z = W self F q₂ → MemInv q₂.2.1 → ∃ L, Small L ∧ Sub q₂.2.1.taken L ∧
      ∀ q₁, Corr L q₁ q₂ → NoBad bad (W self F q₁) → ¬Same Ret x (W self F q₁) := by
  induction hb with
  | ret a b hx hz hn =>
    intro q₂ hq hI
    subst hq
    refine base_case hF q₂ hI (CoFree.Proofs.visible_pure hz) fun y hsh => ?_
    rcases hsh with ⟨b', hy, hz'⟩ | ⟨op, k₁, k₂, -, hz'⟩ <;> rw [hz] at hz' <;> cases hz'
    exact Same.not_bad (.ret a b hx hy hn)
  | mismatch hx hz hn =>
    intro q₂ hq hI
    subst hq
    exact base_case hF q₂ hI hz fun y hsh =>
      Same.not_bad (.mismatch hx (shape_visible hsh) fun hm => hn (shape_visMatch hsh hm))
  | divL f hc h0 hz =>
    intro q₂ hq hI
    subst hq
    exact base_case hF q₂ hI hz fun y hsh => Same.not_bad (.divL f hc h0 (shape_visible hsh))
  | divR f hx hc h0 =>
    intro q₂ hq hI
    subst hq
    exact divR_case hF hx f hc q₂ h0 hI
  | left hx hz _ ih =>
    intro q₂ hq hI
    obtain ⟨L, hs, hsub, hall⟩ := ih q₂ hq hI
    exact ⟨L, hs, hsub, fun q₁ hc hnb hsame => hall q₁ hc hnb (CoFree.Proofs.Same.ustepL hsame hx)⟩
  | @impure x₀ z₀ op k₁ k₂ r hx hz _ ih =>
    intro q₂ hq hI
    subst hq
    obtain ⟨k', hz', hk⟩ := W_impure_inv hz
    have hok := tstep_succ (q' := k' r) hI (by rw [hz']; exact ⟨r, rfl⟩)
    obtain ⟨L, hs, hsub, hall⟩ := ih (k' r) (hk r) hok.inv
    refine ⟨L, hs, sub_trans hok.sub hsub, peel hF hs q₂ fun q₁ hc hst hnb hsame => ?_⟩
    have ht := match_step' (self := self) hc hst
    rw [hz'] at ht
    rcases ht with ⟨u, hu⟩ | ⟨k₁', hy, hcorr⟩
    · exact nobad_contra hF hnb hu
    · have ho := W_obs_impure (F := F) hy
      exact hall _ (hcorr r) (CoFree.Proofs.noBad_impure hnb ho r) (Same.impure_inv_resp hsame hx ho r)
  | both hx hz _ ih =>
    intro q₂ hq hI
    subst hq
    obtain ⟨q₂', hts, rfl⟩ := W_ustep_inv hz
    have hok := tstep_succ hI hts.succ
    obtain ⟨L, hs, hsub, hall⟩ := ih q₂' rfl hok.inv
    refine ⟨L, hs, sub_trans hok.sub hsub, peel hF hs q₂ fun q₁ hc hst hnb hsame => ?_⟩
    have hsame' := CoFree.Proofs.Same.ustepL hsame hx
    have ht := match_step' (self := self) hc hst
    rcases ht with ⟨u, hu⟩ | ht
    · exact nobad_contra hF hnb hu
    rcases hts with h | ⟨c, k, r, h, rfl⟩ <;> rw [h] at ht
    · obtain ⟨q₁', h₁, hcorr⟩ := ht
      have ho := W_obs_silent (F := F) h₁
      exact hall q₁' hcorr (CoFree.Proofs.noBad_silent hnb ho) (Same.silentR_inv hsame' ho)
    · obtain ⟨c', k₁, h₁, hall'⟩ := ht
      obtain ⟨r₁, hcorr⟩ := hall' r hsub
      have ho := W_obs_branch (F := F) h₁
      exact hall _ hcorr (CoFree.Proofs.noBad_branch hnb ho r₁) (Same.branchR_inv hsame' ho r₁)
  | right hx hz _ ih =>
    intro q₂ hq hI
    subst hq
    obtain ⟨q₂', hts, rfl⟩ := W_ustep_inv hz
    have hok := tstep_succ hI hts.succ
    obtain ⟨L, hs, hsub, hall⟩ := ih q₂' rfl hok.inv
    refine ⟨L, hs, sub_trans hok.sub hsub, peel hF hs q₂ fun q₁ hc hst hnb hsame => ?_⟩
    have ht := match_step' (self := self) hc hst
    rcases ht with ⟨u, hu⟩ | ht
    · exact nobad_contra hF hnb hu
    rcases hts with h | ⟨c, k, r, h, rfl⟩ <;> rw [h] at ht
    · obtain ⟨q₁', h₁, hcorr⟩ := ht
      have ho := W_obs_silent (F := F) h₁
      exact hall q₁' hcorr (CoFree.Proofs.noBad_silent hnb ho) (Same.silentR_inv hsame ho)
    · obtain ⟨c', k₁, h₁, hall'⟩ := ht
      obtain ⟨r₁, hcorr⟩ := hall' r hsub
      have ho := W_obs_branch (F := F) h₁
      exact hall _ hcorr (CoFree.Proofs.noBad_branch hnb ho r₁) (Same.branchR_inv hsame ho r₁)

end Transfer

section Root

variable {self : Address} {β : Type} {F : UB ⊕ Outcome → β} {bad : β → Prop}
  {N' : NonDeterminism} {α : Type} {Ret : α → β → Prop}

def root (self : Address) (F : UB ⊕ Outcome → β) (w₀ : World) (m : SirM Empty) :
    CoFree WorldE MemoryND β :=
  (interpHost self w₀ (interpMem m)).bind fun r => CoFree.pure (F r)

def memAt (r : MemoryND.Resp (.pick (Word.size - CompilerReservedBytes) (by decide))) : MemState :=
  { reserved := ⟨r.val, CompilerReservedBytes⟩ }

lemma interp_branch_bind (hs : HostState) (c : MemoryND.Op)
    (g : MemoryND.Resp c → CoFree HostE MemoryND UB) :
    (CoFree.interp (hostStep self) hs ((CoFree.branch c).bind g)).observe =
      .branch c fun r => CoFree.interp (hostStep self) hs ((CoFree.pure r).bind g) := by
  rw [CoFree.Proofs.observe_interp]
  simp only [CoFree.branch]
  rw [CoFree.bind.eq_1]
  rfl

lemma root_observe (w₀ : World) (m : SirM Empty) :
    (root self F w₀ m).observe = .branch (.pick (Word.size - CompilerReservedBytes) (by decide)) fun r =>
      (CoFree.interp (hostStep self) ⟨w₀, .empty⟩ ((CoFree.pure r).bind fun start =>
        CoFree.interp memStep { reserved := ⟨start.val, CompilerReservedBytes⟩ } m)).bind
          fun r => CoFree.pure (F r) := by
  unfold root interpHost
  rw [observe_bind]
  unfold interpMem
  erw [interp_branch_bind]
  rfl

lemma root_bisim (w₀ : World) (m : SirM Empty) (r : MemoryND.Resp (.pick (Word.size - CompilerReservedBytes) (by decide))) :
    Bisim (OpRel.eq WorldE) Eq
      ((CoFree.interp (hostStep self) ⟨w₀, .empty⟩ ((CoFree.pure r).bind fun start =>
        CoFree.interp memStep { reserved := ⟨start.val, CompilerReservedBytes⟩ } m)).bind
          fun r => CoFree.pure (F r))
      (W self F (⟨w₀, .empty⟩, memAt r, m)) :=
  Bisim.bind (Bisim.interp (hostStep self) (DeadCode.hostStep_nat self)
    (Bisim.congr rfl (by rw [observe_bind, observe_pure]; rfl) (Bisim.refl (fun _ => rfl) _)) _)
    fun _ _ h => h ▸ Bisim.refl (fun _ => rfl) _

lemma root_same (hF : ∀ u, bad (F (.inl u))) (x : CoFree WorldE N' α) {m₁ m₂ : SirM Empty}
    (hsk : Skip DeadExtra (fun _ => False) Eq m₁ m₂) (w₀ : World)
    (hnb : NoBad bad (root self F w₀ m₁)) (h : Same Ret x (root self F w₀ m₁)) :
    Same Ret x (root self F w₀ m₂) := by
  refine Same.branchR _ (root_observe w₀ m₂) fun r => ?_
  have h₁ := Same.bisim (Same.branchR_inv h (root_observe w₀ m₁) r) (root_bisim w₀ m₁ r)
  have hnb₁ : NoBad bad (W self F (⟨w₀, .empty⟩, memAt r, m₁)) := fun b hb ho =>
    CoFree.Proofs.noBad_branch hnb (root_observe w₀ m₁) r b hb
      (HasOutcome.bisim ho (Bisim.symm (root_bisim w₀ m₁ r)))
  have hI : MemInv (memAt r) := inv_init r.val r.isLt
  refine Same.bisim (Classical.byContradiction fun hn => ?_) (Bisim.symm (root_bisim (F := F) w₀ m₂ r))
  have hb := Classical.byContradiction fun hnb' => hn (Same.of_not_bad hnb')
  obtain ⟨L, -, -, hall⟩ := transfer hF hb (⟨w₀, .empty⟩, memAt r, m₂) rfl hI
  exact hall (⟨w₀, .empty⟩, memAt r, m₁) ⟨rfl, corr_init L _, hI, hI, hsk⟩ hnb₁ h₁

lemma Same.removeDeadAllocs (F : UB ⊕ Outcome → β) (hF : ∀ u, bad (F (.inl u)))
    (x : CoFree WorldE N' α) {m₁ m₂ : SirM Empty} (self : Address) (w₀ : World)
    (hsk : Skip DeadExtra (fun _ => False) Eq m₁ m₂)
    (hnb : NoBad bad ((interpHost self w₀ (interpMem m₁)).bind fun r => CoFree.pure (F r)))
    (h : Same Ret x ((interpHost self w₀ (interpMem m₁)).bind fun r => CoFree.pure (F r))) :
    Same Ret x ((interpHost self w₀ (interpMem m₂)).bind fun r => CoFree.pure (F r)) :=
  root_same (self := self) (F := F) hF x hsk w₀ hnb h

end Root

end Sir.Proofs.DeadAlloc
