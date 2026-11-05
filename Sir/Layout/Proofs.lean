import Sir.Layout

namespace Sir.Proofs

lemma two_pow_asBits (n : ByteSize) : 2 ^ n.asBits = 256 ^ n.toNat := by
  rw [ByteSize.asBits, Nat.mul_comm, Nat.pow_mul]

lemma size_toBytes (n : ByteSize) (w : Word) : (w.toBytes n).size = n.toNat := by
  simp [Word.toBytes, ByteArray.size]

lemma foldl_bytes_lt (xs : List UInt8) (acc : Nat) (j : Nat) (h : acc < 256 ^ j) :
    xs.foldl (fun acc x => acc * 256 + x.toNat) acc < 256 ^ (j + xs.length) := by
  induction xs generalizing acc j with
  | nil => simpa using h
  | cons x xs ih =>
    have hx : x.toNat < 256 := x.toNat_lt
    have : acc * 256 + x.toNat < 256 ^ (j + 1) := by
      rw [Nat.pow_succ]
      have : (acc + 1) * 256 ≤ 256 ^ j * 256 := Nat.mul_le_mul_right _ h
      rw [Nat.add_mul] at this
      omega
    have := ih _ _ this
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

lemma ofBytes_hasSize (b : ByteArray) (n : ByteSize) (h : b.size ≤ n.toNat) :
    (Word.ofBytes b).HasSize n := by
  have hlt := foldl_bytes_lt b.data.toList 0 0 (by simp)
  have hle : 256 ^ (0 + b.data.toList.length) ≤ 2 ^ n.asBits := by
    rw [two_pow_asBits]
    exact Nat.pow_le_pow_right (by decide) (by rw [Nat.zero_add, Array.length_toList]; exact h)
  have h256 : 2 ^ n.asBits ≤ 2 ^ 256 :=
    Nat.pow_le_pow_right (by decide) (by have := n.valid; unfold ByteSize.asBits; omega)
  simp only [Word.HasSize, Word.ofBytes, Word.ofNat, Word.bits, BitVec.toNat_ofNat]
  rw [← Array.foldl_toList, Nat.mod_eq_of_lt (by omega)]
  omega

lemma foldl_toBytes (n : Nat) (x : Nat) :
    ∀ k ≤ n, ((List.range k).map fun i => (x >>> (8 * (n - 1 - i))).toUInt8).foldl
      (fun acc x => acc * 256 + x.toNat) 0 = (x >>> (8 * (n - k))) % 256 ^ k
  | 0, _ => by simp [Nat.mod_one]
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.foldl_append, foldl_toBytes n x k (by omega)]
    have hm : n - k = (n - 1 - k) + 1 := by omega
    have hm' : n - (k + 1) = n - 1 - k := by omega
    rw [hm, hm', Nat.mul_add, Nat.shiftRight_add, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, Nat.toUInt8,
      UInt8.toNat_ofNat']
    generalize x >>> (8 * (n - 1 - k)) = y
    simp only [Nat.shiftRight_eq_div_pow y 8, show (2 : Nat) ^ 8 = 256 from rfl]
    omega

lemma ofBytes_toBytes (n : ByteSize) (w : Word) (h : w.HasSize n) : Word.ofBytes (w.toBytes n) = w := by
  have := foldl_toBytes n.toNat w.toNat n.toNat (Nat.le_refl _)
  simp only [Word.ofBytes, Word.toBytes, ← Array.foldl_toList, Array.toList_map, Array.toList_range]
  rw [this, Nat.sub_self, Nat.mul_zero, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (by rw [Word.HasSize, two_pow_asBits] at h; exact h)]
  simp [Word.ofNat, Word.bits]

lemma getElem?_eq_data (b : ByteArray) (j : Nat) : b[j]? = b.data[j]? := by
  by_cases h : j < b.size
  · rw [getElem?_pos b j h, Array.getElem?_eq_getElem h]; rfl
  · rw [getElem?_neg b j h, Array.getElem?_eq_none (Nat.not_lt.mp h)]

lemma size_copySlice (v w : ByteArray) (o : Nat) (h : o + v.size ≤ w.size) :
    (v.copySlice 0 w o v.size).size = w.size := by
  simp only [ByteArray.size, ByteArray.copySlice, Array.size_append, Array.size_extract] at *
  omega

lemma data_copySlice (v w : ByteArray) (o j : Nat) (h : o + v.size ≤ w.size) :
    (v.copySlice 0 w o v.size).data[j]? =
      if o ≤ j ∧ j < o + v.size then v.data[j - o]? else w.data[j]? := by
  simp only [ByteArray.size] at h
  simp only [ByteArray.copySlice, Array.getElem?_append, Array.getElem?_extract, Array.size_append,
    Array.size_extract, ByteArray.size]
  split <;> split <;> split <;> (try split) <;> (try split) <;> first | rfl | omega | (congr 1; omega) | (rw [Array.getElem?_eq_none (by omega)])


def SlotsDisjoint (x y : ByteArray × Nat) : Prop := x.2 + x.1.size ≤ y.2 ∨ y.2 + y.1.size ≤ x.2

lemma foldl_copySlice (W : List (ByteArray × Nat)) (w : ByteArray)
    (hb : ∀ x ∈ W, x.2 + x.1.size ≤ w.size) (hd : W.Pairwise SlotsDisjoint) :
    let F := W.foldl (fun m x => x.1.copySlice 0 m x.2 x.1.size) w
    F.size = w.size ∧
      (∀ j, (∀ x ∈ W, ¬(x.2 ≤ j ∧ j < x.2 + x.1.size)) → F.data[j]? = w.data[j]?) ∧
      ∀ x ∈ W, ∀ k < x.1.size, F.data[x.2 + k]? = x.1.data[k]? := by
  induction W generalizing w with
  | nil => simp
  | cons x W ih =>
    have hx := size_copySlice x.1 w x.2 (hb x (by simp))
    obtain ⟨hs, hout, hin⟩ := ih (x.1.copySlice 0 w x.2 x.1.size)
      (fun y hy => hx ▸ hb y (by simp [hy])) (List.pairwise_cons.1 hd).2
    refine ⟨hs.trans hx, fun j hj => ?_, fun y hy k hk => ?_⟩
    · simp only [List.foldl_cons]
      rw [hout j (fun y hy => hj y (by simp [hy])), data_copySlice _ _ _ _ (hb x (by simp)),
        ite_eq_right_of_eq_false _ _ (eq_false (hj x (by simp)))]
    · simp only [List.foldl_cons]
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [hout _ (fun z hz => ?_), data_copySlice _ _ _ _ (hb y (by simp)),
        ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
        · congr 1; omega
        · have := (List.pairwise_cons.1 hd).1 z hz
          simp only [SlotsDisjoint] at this
          omega
      · exact hin y hy k hk

lemma forIn_inv {α σ : Type} (xs : List α) (f : α → σ → Option (ForInStep σ)) (P : σ → Prop)
    (hf : ∀ x ∈ xs, ∀ s r, P s → f x s = some r → P r.value) (init : σ) (hi : P init)
    (s' : σ) (h : forIn xs init f = some s') : P s' := by
  induction xs generalizing init with
  | nil => simp only [List.forIn_nil] at h; cases h; exact hi
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases hx : f x init with
    | none => rw [hx] at h; cases h
    | some r =>
      have hr := hf x (by simp) init r hi hx
      rw [hx] at h
      cases r with
      | done b => cases h; exact hr
      | yield b => exact ih (fun y hy => hf y (by simp [hy])) b hr h

lemma forIn_foldl {α σ : Type} (xs : List α) (f : α → σ → Option (ForInStep σ)) (g : σ → α → σ)
    (P : σ → Prop) (hf : ∀ x ∈ xs, ∀ s, P s → f x s = some (.yield (g s x)))
    (hg : ∀ x ∈ xs, ∀ s, P s → P (g s x)) (init : σ) (hi : P init) :
    forIn xs init f = some (xs.foldl g init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, hf x (by simp) init hi]
    exact ih (fun y hy => hf y (by simp [hy])) (fun y hy => hg y (by simp [hy])) _
      (hg x (by simp) init hi)

lemma getElem_foldl_set {α : Type} {n : Nat} (xs : List (Fin n)) (v : Fin n → α) (init : Vector α n)
    (j : Fin n) :
    (xs.foldl (fun s i => s.set i (v i) i.isLt) init)[j] = if j ∈ xs then v j else init[j] := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    by_cases hj : j ∈ xs
    · simp [hj]
    · by_cases hx : j = x
      · subst hx; simp [hj]
      · simp [hj, hx, Fin.val_ne_of_ne (Ne.symm hx)]

lemma mapM_id_eq_some {α : Type} {n : Nat} (xs : Vector (Option α) n) (ys : Vector α n)
    (h : xs.mapM id = some ys) : xs = ys.map some := by
  have h' := congrArg (Functor.map Vector.toArray) h
  rw [Vector.toArray_mapM, Array.mapM_eq_mapM_toList] at h'
  have hl : ∀ (l : List (Option α)) (r : List α), l.mapM id = some r → l = r.map some := by
    intro l
    induction l with
    | nil => intro r h; simp at h; simp [← h]
    | cons a l ih =>
      intro r h
      cases a with
      | none => simp at h
      | some a =>
        simp only [List.mapM_cons, id] at h
        cases hl : l.mapM id with
        | none => simp [hl] at h
        | some r' =>
          simp [hl] at h
          simp [← h, ih r' hl]
  cases hm : xs.toArray.toList.mapM id with
  | none => simp [hm] at h'
  | some r =>
    simp [hm] at h'
    apply Vector.toArray_inj.1
    apply Array.toList_inj.1
    simp [hl _ _ hm, ← h']


variable {p : Program}

lemma size_zeros (n : ByteSize) : (zeros n).size = n.toNat := by
  simp [zeros, ByteArray.size]

lemma offset_add_le {c : ByteArray} {n : ByteSize} (o : MappingOffset c (zeros n)) :
    o.val.toNat + n.toNat ≤ c.size := by
  have hn := n.valid.1
  have h := o.property (n.toNat - 1) (by rw [size_zeros]; omega)
  refine Classical.byContradiction fun hc => ?_
  rw [getElem?_neg c _ (by omega)] at h
  cases h

def slotWrites (l : Layout p) (slots : Vector Word p.immutables.size) : List (ByteArray × Nat) :=
  (List.finRange p.immutables.size).flatMap fun i =>
    (l.immutableOffsets i).map fun o => (slots[i].toBytes p.immutables[i], o.val.toNat)

lemma setImmutables_eq_foldl (l : Layout p) (slots : Vector Word p.immutables.size) :
    l.setImmutables slots =
      (slotWrites l slots).foldl (fun m x => x.1.copySlice 0 m x.2 x.1.size) l.main := by
  simp [Layout.setImmutables, slotWrites, List.foldl_flatMap, List.foldl_map]

lemma slotWrites_bounds (l : Layout p) (slots : Vector Word p.immutables.size) :
    ∀ x ∈ slotWrites l slots, x.2 + x.1.size ≤ l.main.size := by
  intro x hx
  simp only [slotWrites, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨i, -, o, -, rfl⟩ := hx
  rw [size_toBytes]
  exact offset_add_le o

lemma slotWrites_pairwise (l : Layout p) (slots : Vector Word p.immutables.size) :
    (slotWrites l slots).Pairwise SlotsDisjoint := by
  have hd : ∀ i i' (a : Fin (l.immutableOffsets i).length) (b : Fin (l.immutableOffsets i').length),
      ¬(i = i' ∧ a ≍ b) →
      SlotsDisjoint (slots[i].toBytes p.immutables[i], (l.immutableOffsets i)[a].val.toNat)
        (slots[i'].toBytes p.immutables[i'], (l.immutableOffsets i')[b].val.toNat) := by
    intro i i' a b hne
    rcases l.no_imm_imm_overlap i i' a b with h | h
    · exact absurd h hne
    · simpa [SlotsDisjoint, NatRange.Disjoint, NatRange.end, MappingOffset.range, size_toBytes,
        size_zeros] using h
  simp only [slotWrites, List.pairwise_flatMap, List.pairwise_map]
  refine ⟨fun i _ => List.pairwise_iff_getElem.2 fun a b ha hb hab =>
    hd i i ⟨a, ha⟩ ⟨b, hb⟩ fun ⟨_, h⟩ => ?_, (List.nodup_finRange _).imp fun {i i'} hii' => ?_⟩
  · have := Fin.val_eq_of_eq (eq_of_heq h)
    simp at this
    omega
  · intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨o, ho, rfl⟩ := hx
    obtain ⟨o', ho', rfl⟩ := hy
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem ho
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem ho'
    exact hd i i' ⟨a, ha⟩ ⟨b, hb⟩ fun ⟨h, _⟩ => hii' h

lemma setImmutables_facts (l : Layout p) (slots : Vector Word p.immutables.size) :
    (l.setImmutables slots).size = l.main.size ∧
      ∀ i, ∀ o ∈ l.immutableOffsets i, ∀ k < p.immutables[i].toNat,
        (l.setImmutables slots).data[o.val.toNat + k]? = (slots[i].toBytes p.immutables[i]).data[k]? := by
  obtain ⟨hs, -, hin⟩ := foldl_copySlice (slotWrites l slots) l.main (slotWrites_bounds l slots)
    (slotWrites_pairwise l slots)
  rw [setImmutables_eq_foldl]
  refine ⟨hs, fun i o ho k hk => hin (slots[i].toBytes p.immutables[i], o.val.toNat) ?_ k
    (by rw [size_toBytes]; exact hk)⟩
  simp only [slotWrites, List.mem_flatMap, List.mem_map]
  exact ⟨i, List.mem_finRange i, o, ho, rfl⟩

lemma guard_eq_some {c : Prop} [Decidable c] {u : Unit} (h : (guard c : Option Unit) = some u) : c := by
  by_cases hc : c
  · exact hc
  · simp [guard, hc, failure] at h

lemma getElem_set_fin {α : Type} {n : Nat} (s : Vector α n) (x j : Fin n) (a : α) :
    (s.set x a x.isLt)[j] = if j = x then a else s[j] := by
  by_cases h : j = x
  · subst h; simp
  · simp only [Fin.getElem_fin, h, ↓reduceIte]
    exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne (Ne.symm h))

lemma extractImmutables_some (l : Layout p) (b t : ByteArray) (vs : Array Word)
    (h : l.extractImmutables b = some (t, vs)) :
    ∃ values : Vector Word p.immutables.size, vs = values.toArray ∧ l.setImmutables values ++ t = b ∧
      t = b.extract l.main.size b.size ∧ ∀ i : Fin p.immutables.size, values[i].HasSize p.immutables[i] := by
  simp only [Layout.extractImmutables, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, s', hloop, values, hmap, _, hguard, hret⟩ := h
  cases hret
  refine ⟨values, rfl, guard_eq_some hguard, rfl, fun i => ?_⟩
  let P : Vector (Option Word) p.immutables.size → Prop :=
    fun s => ∀ (j : Fin p.immutables.size) v, s[j] = some v → v.HasSize p.immutables[j]
  have hP : P s' := by
    refine forIn_inv _ _ P (fun x _ s r hs hr => ?_) _ (fun j v h => by simp at h) _ hloop
    rw [Option.bind_eq_some_iff] at hr
    obtain ⟨s₂, hin, hr⟩ := hr
    cases hr
    refine forIn_inv _ _ P (fun o _ s r hs hr => ?_) _ hs _ hin
    split at hr
    · rw [Option.bind_eq_some_iff] at hr
      obtain ⟨_, -, hr⟩ := hr
      cases hr
      exact hs
    · cases hr
      intro j v hv
      simp only [ForInStep.value, getElem_set_fin] at hv
      split at hv
      · subst_vars
        cases hv
        exact ofBytes_hasSize _ _ (by rw [ByteArray.size_extract]; omega)
      · exact hs j v hv
  exact hP i _ (by rw [mapM_id_eq_some s' values hmap]; simp)

lemma foldl_set_const {α : Type} {β : Type} {n : Nat} (xs : List β) (i : Nat) (a : α) (hi : i < n)
    (s : Vector α n) (hxs : xs ≠ []) : xs.foldl (fun s _ => s.set i a hi) s = s.set i a hi := by
  induction xs generalizing s with
  | nil => exact absurd rfl hxs
  | cons x xs ih =>
    rw [List.foldl_cons]
    by_cases h : xs = []
    · subst h; rfl
    · rw [ih _ h, Vector.set_set]

lemma extract_setImmutables (l : Layout p) (v : Vector Word p.immutables.size) (t : ByteArray)
    (hv : ∀ i : Fin p.immutables.size, v[i].HasSize p.immutables[i]) (i : Fin p.immutables.size)
    (o : MappingOffset l.main (zeros p.immutables[i])) (ho : o ∈ l.immutableOffsets i) :
    Word.ofBytes ((l.setImmutables v ++ t).extract o.val.toNat (o.val.toNat + p.immutables[i].toNat)) =
      v[i] := by
  obtain ⟨hsize, hslot⟩ := setImmutables_facts l v
  have hle := offset_add_le o
  rw [ByteArray.extract_append,
    show o.val.toNat + p.immutables[i].toNat - (l.setImmutables v).size = 0 by omega,
    show ∀ (b : ByteArray) j, b.extract j 0 = .empty from fun _ _ => by ext1; simp,
    ByteArray.append_empty]
  conv => rhs; rw [← ofBytes_toBytes _ _ (hv i)]
  congr 1
  apply ByteArray.ext
  apply Array.ext_getElem?
  intro k
  rw [ByteArray.data_extract, Array.getElem?_extract]
  have hsize' : (l.setImmutables v).data.size = l.main.size := hsize
  by_cases hk : k < p.immutables[i].toNat
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hsize']; omega)), hslot i o ho k hk]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hsize']; omega)), Array.getElem?_eq_none]
    have := size_toBytes p.immutables[i] v[i]
    simp only [ByteArray.size] at this
    omega

lemma extractImmutables_setImmutables (l : Layout p) (v : Vector Word p.immutables.size) (t : ByteArray)
    (hv : ∀ i : Fin p.immutables.size, v[i].HasSize p.immutables[i]) :
    l.extractImmutables (l.setImmutables v ++ t) = some (t, v.toArray) := by
  obtain ⟨hsize, -⟩ := setImmutables_facts l v
  have htail : (l.setImmutables v ++ t).extract l.main.size (l.setImmutables v ++ t).size =
      t := by
    exact ByteArray.extract_append_eq_right hsize.symm (by rw [ByteArray.size_append])
  let P : Vector (Option Word) p.immutables.size → Prop :=
    fun s => ∀ j : Fin p.immutables.size, s[j] = none ∨ s[j] = some v[j]
  have hPset : ∀ (s : Vector (Option Word) p.immutables.size) (x : Fin p.immutables.size), P s →
      P (s.set x (some v[x]) x.isLt) := by
    intro s x hs j
    rw [getElem_set_fin]
    split
    · subst_vars; simp
    · exact hs j
  have hge : ((l.setImmutables v ++ t).size ≥ l.main.size) = True :=
    eq_true (by rw [ByteArray.size_append]; omega)
  simp only [Layout.extractImmutables, htail, hge]
  rw [forIn_foldl (g := fun s (x : Fin p.immutables.size) => s.set x (some v[x]) x.isLt) (P := P)]
  · have hfold : (List.finRange p.immutables.size).foldl (fun s x => s.set x (some v[x]) x.isLt)
        (Vector.replicate p.immutables.size none) = v.map some := by
      apply Vector.ext
      intro j hj
      have := getElem_foldl_set (List.finRange p.immutables.size) (fun x => some v[x])
        (Vector.replicate p.immutables.size none) ⟨j, hj⟩
      simpa [List.mem_finRange] using this
    have hmap : v.mapM some = some v :=
      (Vector.mapM_pure (m := Option) (xs := v) id).trans (by simp)
    rw [hfold]
    simp [hmap, guard]
  · intro x _ s hs
    rw [forIn_foldl (g := fun s _ => s.set x (some v[x]) x.isLt) (P := P)]
    · rw [foldl_set_const _ _ _ _ _ (List.ne_nil_of_length_pos (l.atLeastOne_immOffsets x))]
      rfl
    · intro o ho s hs
      rw [extract_setImmutables l v t hv x o ho]
      split
      · rename_i v' hv'
        rcases hs x with h | h <;> rw [h] at hv' <;> cases hv'
        simp only [guard, Option.bind_eq_bind]
        simp only [↓reduceIte]
        show some (ForInStep.yield s) = _
        congr 2
        apply Vector.ext
        intro j hj
        show s[(⟨j, hj⟩ : Fin _)] = (s.set x (some v[x]) x.isLt)[(⟨j, hj⟩ : Fin _)]
        rw [getElem_set_fin]
        split
        · subst_vars; exact h
        · rfl
      · rfl
    · intro _ _ s hs; exact hPset s x hs
    · exact hs
  · intro x _ s hs; exact hPset s x hs
  · intro j; simp

lemma withSetImmutables_eq_some (l : Layout p) (imms : MainImmutables) (b : ByteArray) :
    l.withSetImmutables imms = some b ↔
      ∃ h : imms.WF p, l.setImmutables ⟨imms.slots, h.1⟩ ++ imms.tail = b := by
  unfold Layout.withSetImmutables
  split <;> simp_all

theorem extractImmutables_withSetImmutables (l : Layout p) (imms : MainImmutables) (b : ByteArray)
    (h : l.withSetImmutables imms = some b) :
    l.extractImmutables b = some (imms.tail, imms.slots) := by
  obtain ⟨hwf, rfl⟩ := (withSetImmutables_eq_some l imms b).1 h
  exact extractImmutables_setImmutables l _ _ hwf.2

theorem extractImmutables_eq_map (l : Layout p) (b : ByteArray) :
    l.extractImmutables b = (l.toMainImmutables b).map fun m => (m.tail, m.slots) := by
  simp [Layout.toMainImmutables, Option.map_map, Function.comp_def]

theorem toMainImmutables_wf (l : Layout p) (b : ByteArray) (imms : MainImmutables)
    (h : l.toMainImmutables b = some imms) : imms.WF p := by
  simp only [Layout.toMainImmutables, Option.map_eq_some_iff] at h
  obtain ⟨⟨t, vs⟩, he, rfl⟩ := h
  obtain ⟨values, rfl, -, -, hsz⟩ := extractImmutables_some l b t _ he
  exact ⟨values.size_toArray, hsz⟩

theorem toMainImmutables_eq_some_iff (l : Layout p) (b : ByteArray) (imms : MainImmutables) :
    l.toMainImmutables b = some imms ↔ l.withSetImmutables imms = some b := by
  constructor
  · intro h
    refine (withSetImmutables_eq_some l imms b).2 ⟨toMainImmutables_wf l b imms h, ?_⟩
    simp only [Layout.toMainImmutables, Option.map_eq_some_iff] at h
    obtain ⟨⟨t, vs⟩, he, rfl⟩ := h
    obtain ⟨values, rfl, hb, -, -⟩ := extractImmutables_some l b t _ he
    exact hb
  · intro h
    simp [Layout.toMainImmutables, extractImmutables_withSetImmutables l imms b h]

theorem extractImmutables_isSome_iff (l : Layout p) (b : ByteArray) :
    (l.extractImmutables b).isSome ↔ ∃ imms : MainImmutables, l.withSetImmutables imms = some b := by
  rw [extractImmutables_eq_map, Option.isSome_map]
  simp only [Option.isSome_iff_exists, toMainImmutables_eq_some_iff]

end Sir.Proofs
