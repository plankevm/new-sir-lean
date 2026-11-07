import Sir.Passes.RemoveUnusedLets
import Sir.WellFormed.Proofs
import ITree.Skip.Theorems
import Sir.Passes.DeadCode.Proofs
import Sir.Passes.RemoveUnusedLets.DeadAlloc.Theorems
import ITree.Refute.Theorems

open Host CoFree

namespace Sir.Proofs.RemoveUnusedLets

open Sir.RemoveUnusedLets

lemma mapM_congr {α β : Type} {f g : α → SirM β} (xs : Array α) (h : ∀ x ∈ xs, f x = g x) :
    xs.mapM f = xs.mapM g := by
  have aux : ∀ n i (bs : Array β), xs.size - i = n →
      arrayMapM_map% f xs i bs = arrayMapM_map% g xs i bs := by
    intro n
    induction n with
    | zero =>
      intro i bs hn
      rw [arrayMapM_map_eq%, arrayMapM_map_eq%]
      split
      · omega
      · rfl
    | succ n ih =>
      intro i bs hn
      rw [arrayMapM_map_eq%, arrayMapM_map_eq%]
      split
      · rename_i hlt
        rw [h _ (Array.getElem_mem hlt)]
        congr 1
        funext b
        exact ih _ _ (by omega)
      · rfl
  unfold Array.mapM
  exact aux _ 0 _ rfl

def Dead (dead : Array Bool) (x : VarId) : Prop := dead[x.id]? = some true

def VarsAgree (dead : Array Bool) (v₁ v₂ : Vars) : Prop := ∀ x, ¬Dead dead x → v₁[x]? = v₂[x]?

lemma compare_eq_iff (a b : VarId) : compare a b = .eq ↔ a = b := by
  rw [varId_compare, Nat.compare_eq_eq]
  cases a; cases b; simp

lemma agree_insert {d : Array Bool} {v₁ v₂ : Vars} (h : VarsAgree d v₁ v₂) (k : VarId) (w : Word) :
    VarsAgree d (v₁.insert k w) (v₂.insert k w) := by
  intro x hx
  rw [Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_insert, h x hx]

lemma agree_insert_dead {d : Array Bool} {v₁ v₂ : Vars} (h : VarsAgree d v₁ v₂) {k : VarId}
    (hk : Dead d k) (w : Word) : VarsAgree d (v₁.insert k w) v₂ := by
  intro x hx
  rw [Std.TreeMap.getElem?_insert]
  split
  · rename_i he
    rw [compare_eq_iff] at he
    subst he
    exact (hx hk).elim
  · exact h x hx

lemma agree_foldl_insert {d : Array Bool} : ∀ (l : List (VarId × Word)) {v₁ v₂ : Vars},
    VarsAgree d v₁ v₂ → VarsAgree d (l.foldl (fun t (x : VarId × Word) => t.insert x.1 x.2) v₁)
      (l.foldl (fun t (x : VarId × Word) => t.insert x.1 x.2) v₂)
  | [], _, _, h => h
  | _ :: l, _, _, h => agree_foldl_insert l (agree_insert h _ _)

lemma lookup_eq {d : Array Bool} {v₁ v₂ : Vars} (h : VarsAgree d v₁ v₂) {x : VarId}
    (hx : ¬Dead d x) : v₁.lookup x = v₂.lookup x := by
  unfold Vars.lookup; rw [h x hx]

lemma lookupAll_eq {d : Array Bool} {v₁ v₂ : Vars} (h : VarsAgree d v₁ v₂) {xs : Array VarId}
    (hx : ∀ x ∈ xs, ¬Dead d x) : v₁.lookupAll xs = v₂.lookupAll xs :=
  mapM_congr xs fun x hm => lookup_eq h (hx x hm)

section Resolve

variable {l₁ l₂ : VarId → SirM Word}

lemma expr_resolve_congr (e : Expr VarId) (h : ∀ x ∈ e.reads, l₁ x = l₂ x) :
    e.resolve l₁ = e.resolve l₂ := by
  cases e <;> simp only [Expr.reads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [Expr.resolve, h]

lemma stmt_resolve_congr (s : Stmt VarId) (h : ∀ x ∈ s.reads, l₁ x = l₂ x) :
    s.resolve l₁ = s.resolve l₂ := by
  cases s <;> simp only [Stmt.reads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [Stmt.resolve, h]

end Resolve

lemma op_resolve_congr {d : Array Bool} {v₁ v₂ : Vars} (hv : VarsAgree d v₁ v₂)
    (op : Operation VarId) (h : ∀ x ∈ op.reads, ¬Dead d x) :
    op.resolve v₁.lookup = op.resolve v₂.lookup := by
  cases op with
  | «let» out e =>
    simp only [Operation.resolve]
    rw [expr_resolve_congr e fun x hx => lookup_eq hv (h x hx)]
  | stmt s =>
    simp only [Operation.resolve]
    rw [stmt_resolve_congr s fun x hx => lookup_eq hv (h x hx)]
  | icall g ins outs =>
    simp only [Operation.resolve]
    rw [mapM_congr ins fun x hx => lookup_eq hv (h x (by simpa [Operation.reads] using hx))]

lemma ctrl_resolve_congr {d : Array Bool} {v₁ v₂ : Vars} (hv : VarsAgree d v₁ v₂)
    (c : Control VarId) (h : ∀ x ∈ c.reads, ¬Dead d x) :
    c.resolve v₁.lookup = c.resolve v₂.lookup := by
  cases c <;> simp only [Control.reads, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [Control.resolve]
  all_goals first
    | rfl
    | rw [lookup_eq hv h]
    | rw [lookup_eq hv h.1, lookup_eq hv h.2]
    | rw [mapM_congr _ fun x hx => lookup_eq hv (h x (by simpa using hx))]

section Algorithm

lemma count_varId (l : List VarId) (u : VarId) (w : Nat) :
    (u :: l).count ⟨w⟩ = l.count ⟨w⟩ + if u.id = w then 1 else 0 := by
  rw [List.count_cons]
  congr 1
  obtain ⟨u⟩ := u
  by_cases h : u = w <;> simp [h]

lemma foldl_modify_add (l : List VarId) (us : Array Nat) (w : Nat) :
    (l.foldl (fun us u => us.modify u.id (· + 1)) us)[w]? = us[w]?.map (· + l.count ⟨w⟩) := by
  induction l generalizing us with
  | nil => simp
  | cons u l ih =>
    rw [List.foldl_cons, ih, Array.getElem?_modify, count_varId]
    by_cases h : u.id = w
    · subst h; cases us[u.id]? <;> simp; omega
    · simp [h]

lemma foldl_modify_sub (l : List VarId) (us : Array Nat) (w : Nat) :
    (l.foldl (fun us u => us.modify u.id (· - 1)) us)[w]? = us[w]?.map (· - l.count ⟨w⟩) := by
  induction l generalizing us with
  | nil => simp
  | cons u l ih =>
    rw [List.foldl_cons, ih, Array.getElem?_modify, count_varId]
    by_cases h : u.id = w
    · subst h; cases us[u.id]? <;> simp; omega
    · simp [h]

lemma foldl_foldl_add {α : Type} (xs : List α) (g : α → List VarId) (us : Array Nat) (w : Nat) :
    (xs.foldl (fun us a => (g a).foldl (fun us u => us.modify u.id (· + 1)) us) us)[w]? =
      us[w]?.map (· + (xs.map fun a => (g a).count ⟨w⟩).sum) := by
  induction xs generalizing us with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons, ih, foldl_modify_add]
    cases us[w]? <;> simp; omega

def flatOps (fn : Function) : List (Operation VarId) := fn.blocks.toList.flatMap (·.ops.toList)

def extraReads (fn : Function) : List VarId :=
  fn.blocks.toList.flatMap fun b => b.control.reads ++ b.outputs.toList

def usesIn (fn : Function) (dead : Array Bool) (u : VarId) : Nat :=
  ((flatOps fn).map fun op => if op.isDeadLet dead then 0 else op.reads.count u).sum +
    (extraReads fn).count u

def defOf (v : Nat) (op : Operation VarId) : Option (List VarId) :=
  match op.removableLet? with
  | some (out, rs) => if out.id = v then some rs else none
  | none => none

lemma ops_toList (fn : Function) : (fn.blocks.flatMap (·.ops)).toList = flatOps fn := by
  simp [flatOps, Array.toList_flatMap]

lemma countUses_spec (n : Nat) (fn : Function) (w : Nat) (hw : w < n) :
    (countUses n (fn.blocks.flatMap (·.ops)) fn.blocks)[w]? =
      some (((flatOps fn).map fun op => op.reads.count ⟨w⟩).sum + (extraReads fn).count ⟨w⟩) := by
  unfold countUses
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure,
    Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList]
  rw [ops_toList]
  show (List.foldl (fun us b => (b.control.reads ++ b.outputs.toList).foldl
    (fun us u => us.modify u.id (· + 1)) us) (List.foldl (fun us op => op.reads.foldl
    (fun us u => us.modify u.id (· + 1)) us) (Array.replicate n 0) (flatOps fn))
    fn.blocks.toList)[w]? = _
  rw [foldl_foldl_add, foldl_foldl_add, Array.getElem?_replicate]
  simp only [hw, ↓reduceIte]
  simp [extraReads, List.count_flatMap, Function.comp_def]

def addDef (op : Operation VarId) (d : Array (List (List VarId))) : Array (List (List VarId)) :=
  match op.removableLet? with
  | some (out, reads) => d.modify out.id (reads :: ·)
  | none => d

lemma forIn_collectDefs (f : Operation VarId → Array (List (List VarId)) →
    Id (ForInStep (Array (List (List VarId)))))
    (hf : ∀ op d, f op d = Pure.pure (.yield (addDef op d)))
    (l : List (Operation VarId)) (defs : Array (List (List VarId))) (w : Nat) :
    (forIn l defs f).run[w]? = defs[w]?.map ((l.filterMap (defOf w)).reverse ++ ·) := by
  induction l generalizing defs with
  | nil => rcases h : defs[w]? <;> simp [h]
  | cons op l ih =>
    rw [List.forIn_cons, List.filterMap_cons, hf]
    show (forIn l (addDef op defs) f).run[w]? = _
    rw [ih]
    unfold addDef
    rcases h : op.removableLet? with _ | ⟨out, rs⟩
    · have hd : defOf w op = none := by simp [defOf, h]
      simp [hd]
    · rw [Array.getElem?_modify]
      by_cases ho : out.id = w
      · have hd : defOf w op = some rs := by simp [defOf, h, ho]
        subst ho; cases defs[out.id]? <;> simp [hd]
      · have hd : defOf w op = none := by simp [defOf, h, ho]
        simp [ho, hd]

lemma collectDefs_spec (n : Nat) (fn : Function) (w : Nat) (hw : w < n) :
    (collectDefs n (fn.blocks.flatMap (·.ops)))[w]? =
      some ((flatOps fn).filterMap (defOf w)).reverse := by
  unfold collectDefs
  simp only [bind_pure]
  rw [← Array.forIn_toList, ops_toList, forIn_collectDefs _ (fun op d => by
    unfold addDef; rcases op.removableLet? with _ | ⟨_, _⟩ <;> rfl), Array.getElem?_replicate]
  simp [hw]

lemma reads_of_removableLet {op : Operation VarId} {out : VarId} {rs : List VarId}
    (h : op.removableLet? = some (out, rs)) : op.reads = rs := by
  cases op with
  | «let» o e =>
    simp only [Operation.removableLet?] at h
    split at h
    · cases h; rfl
    · cases h
  | _ => cases h

lemma term_set {dead : Array Bool} {v : Nat} (hv : dead[v]? = some false) (u : VarId)
    (op : Operation VarId) :
    (if op.isDeadLet dead then 0 else op.reads.count u) =
      (if op.isDeadLet (dead.setIfInBounds v true) then 0 else op.reads.count u) +
      (match defOf v op with | some rs => rs.count u | none => 0) := by
  have hlt : v < dead.size := by
    rcases Nat.lt_or_ge v dead.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hv; cases hv
  unfold defOf Operation.isDeadLet
  rcases h : op.removableLet? with _ | ⟨out, rs⟩
  · simp
  · rw [reads_of_removableLet h]
    by_cases ho : out.id = v
    · subst ho
      have hf : dead[out.id] = false := by
        rw [Array.getElem?_eq_getElem hlt] at hv; exact Option.some.inj hv
      simp [hlt, hf]
    · simp [Ne.symm ho, ho]

lemma usesIn_set (fn : Function) {dead : Array Bool} {v : Nat} (hv : dead[v]? = some false)
    (u : VarId) : usesIn fn dead u = usesIn fn (dead.setIfInBounds v true) u +
      (((flatOps fn).filterMap (defOf v)).map (·.count u)).sum := by
  unfold usesIn
  suffices ∀ l : List (Operation VarId), (l.map fun op => if op.isDeadLet dead then 0 else op.reads.count u).sum =
      (l.map fun op => if op.isDeadLet (dead.setIfInBounds v true) then 0 else op.reads.count u).sum +
      ((l.filterMap (defOf v)).map (·.count u)).sum by rw [this]; omega
  intro l
  induction l with
  | nil => rfl
  | cons op l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.filterMap_cons, ih,
      term_set hv u op]
    rcases defOf v op with _ | rs
    · simp only; omega
    · simp only [List.map_cons, List.sum_cons]; omega

structure Inv (fn : Function) (n : Nat) (uses : Array Nat) (dead : Array Bool) : Prop where
  size : dead.size = n
  count : ∀ w < n, uses[w]? = some (usesIn fn dead ⟨w⟩)
  zero : ∀ w : Nat, dead[w]? = some true → uses[w]? = some 0

lemma forIn_fst_foldl {α γ : Type} (step : Array Nat → α → Array Nat)
    (g : α → Array Nat × γ → Id (ForInStep (Array Nat × γ)))
    (hg : ∀ a s, ∃ c, g a s = Pure.pure (.yield (step s.1 a, c))) :
    ∀ (l : List α) (s : Array Nat × γ), (forIn l s g).run.1 = l.foldl step s.1
  | [], _ => rfl
  | a :: l, s => by
    obtain ⟨c, hc⟩ := hg a s
    rw [List.forIn_cons, hc, List.foldl_cons]
    exact forIn_fst_foldl step g hg l _

lemma release_inner (reads : List VarId) (us wk : Array Nat) :
    (forIn (m := Id) reads (us, wk) fun u s =>
      if (s.1.modify u.id (· - 1))[u.id]? = some 0 then
        Pure.pure (ForInStep.yield (s.1.modify u.id (· - 1), s.2.push u.id))
      else Pure.pure (ForInStep.yield (s.1.modify u.id (· - 1), s.2))).run.1 =
      reads.foldl (fun us u => us.modify u.id (· - 1)) us := by
  induction reads generalizing us wk with
  | nil => rfl
  | cons u reads ih =>
    rw [List.forIn_cons, List.foldl_cons]
    split <;> exact ih _ _

lemma release_fst (readss : List (List VarId)) (uses work : Array Nat) :
    (release readss uses work).1 =
      readss.foldl (fun us rs => rs.foldl (fun us u => us.modify u.id (· - 1)) us) uses := by
  unfold release
  dsimp only [Id.run_bind, Id.run_pure]
  induction readss generalizing uses work with
  | nil => rfl
  | cons rs readss ih =>
    rw [List.forIn_cons, List.foldl_cons, ← release_inner rs uses work]
    exact ih _ _

lemma release_spec (readss : List (List VarId)) (uses work : Array Nat) (w : Nat) :
    (release readss uses work).1[w]? = uses[w]?.map (· - (readss.map (·.count ⟨w⟩)).sum) := by
  rw [release_fst]
  induction readss generalizing uses with
  | nil => rcases h : uses[w]? <;> simp [h]
  | cons rs readss ih =>
    rw [List.foldl_cons, ih, foldl_modify_sub]
    cases uses[w]? <;> simp; omega

lemma inv_step {fn : Function} {n : Nat} {uses : Array Nat} {dead : Array Bool} {v : Nat}
    (h : Inv fn n uses dead) (hv : dead[v]? = some false) (hu : uses[v]? = some 0)
    (work : Array Nat) :
    Inv fn n (release ((flatOps fn).filterMap (defOf v)).reverse uses work).1
      (dead.setIfInBounds v true) := by
  have hlt : v < n := by
    rw [← h.size]
    rcases Nat.lt_or_ge v dead.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hv; cases hv
  have hsum : ∀ w, ((((flatOps fn).filterMap (defOf v)).reverse.map (·.count ⟨w⟩)).sum) =
      ((((flatOps fn).filterMap (defOf v)).map (·.count ⟨w⟩)).sum) := by
    intro w; rw [List.map_reverse, List.sum_reverse]
  refine ⟨by rw [Array.size_setIfInBounds, h.size], fun w hw => ?_, fun w hw => ?_⟩
  · rw [release_spec, h.count w hw, hsum, usesIn_set fn hv]
    simp
  · rw [release_spec, hsum]
    rw [Array.getElem?_setIfInBounds] at hw
    by_cases hwv : v = w
    · subst hwv
      rw [h.count v hlt]
      have := usesIn_set fn hv ⟨v⟩
      rw [h.count v hlt] at hu
      simp only [Option.some.injEq] at hu
      simp; omega
    · simp only [hwv, ↓reduceIte] at hw
      rw [h.zero w hw]
      simp

lemma isDeadLet_replicate (n : Nat) (op : Operation VarId) :
    op.isDeadLet (Array.replicate n false) = false := by
  unfold Operation.isDeadLet
  rcases op.removableLet? with _ | ⟨out, _⟩
  · rfl
  · simp only [Array.getElem?_replicate]
    split <;> rfl

lemma inv_init (fn : Function) (n : Nat) :
    Inv fn n (countUses n (fn.blocks.flatMap (·.ops)) fn.blocks) (Array.replicate n false) := by
  refine ⟨Array.size_replicate, fun w hw => ?_, fun w hw => ?_⟩
  · rw [countUses_spec n fn w hw]
    simp [usesIn, isDeadLet_replicate]
  · rw [Array.getElem?_replicate] at hw
    split at hw <;> cases hw

lemma le_sum_map {α : Type} (f : α → Nat) {x : α} : ∀ {l : List α}, x ∈ l → f x ≤ (l.map f).sum
  | _ :: _, .head _ => by simp
  | _ :: _, .tail _ h => by simp only [List.map_cons, List.sum_cons]; have := le_sum_map f h; omega

lemma deadVars_inv (fn : Function) : ∃ n uses, Inv fn n uses fn.deadVars := by
  unfold Function.deadVars
  dsimp only [Id.run_bind, Id.run_pure]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  refine ⟨?N, _, DeadCode.forIn_range'_inv (fun _ (s : Array Nat × Array Bool × Array Nat) => Inv fn ?N s.1 s.2.1) _ ?step _ 0 _ ?init⟩
  case init => exact inv_init fn _
  case step =>
    rintro k ⟨uses, dead, work⟩ h
    dsimp only at h ⊢
    split
    · rename_i v _
      split
      · rename_i hc
        obtain ⟨hv, hu⟩ := hc
        have hlt : v < dead.size := by
          rcases Nat.lt_or_ge v dead.size with h | h
          · exact h
          · rw [Array.getElem?_eq_none h] at hv; cases hv
        rw [h.size] at hlt
        split
        · rename_i readss hd
          rw [collectDefs_spec _ fn v hlt] at hd
          cases hd
          exact inv_step h hv hu _
        · rename_i hd
          rw [collectDefs_spec _ fn v hlt] at hd
          exact (hd _ rfl).elim
      · exact h
    · intro _ _
      exact h

lemma deadVars_sound (fn : Function) :
    (∀ op ∈ flatOps fn, op.isDeadLet fn.deadVars = false →
      ∀ u ∈ op.reads, fn.deadVars[u.id]? ≠ some true) ∧
    (∀ u ∈ extraReads fn, fn.deadVars[u.id]? ≠ some true) := by
  obtain ⟨n, uses, h⟩ := deadVars_inv fn
  have hz : ∀ u : VarId, fn.deadVars[u.id]? = some true → usesIn fn fn.deadVars u = 0 := by
    intro u hd
    have hlt : u.id < n := by
      rw [← h.size]
      rcases Nat.lt_or_ge u.id fn.deadVars.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hd; cases hd
    have := h.count u.id hlt
    rw [h.zero u.id hd] at this
    exact (Option.some.inj this).symm
  refine ⟨fun op hop hk u hu hd => ?_, fun u hu hd => ?_⟩
  · have h1 := hz u hd
    have h2 := le_sum_map (fun op => if op.isDeadLet fn.deadVars then 0 else op.reads.count u) hop
    have h3 : 0 < op.reads.count u := List.count_pos_iff.2 hu
    simp only [hk] at h2
    unfold usesIn at h1
    simp at h2
    omega
  · have h1 := hz u hd
    have h3 : 0 < (extraReads fn).count u := List.count_pos_iff.2 hu
    unfold usesIn at h1
    omega

end Algorithm

section Extra

abbrev ExtraTo {α : Type} (R : α → Prop) (m : SirM α) : Prop :=
  Skip DeadExtra (fun _ => False) (fun a (_ : PUnit) => R a) m (CoFree.pure ⟨⟩)

abbrev AllExtra {α : Type} (m : SirM α) : Prop := ExtraTo (fun _ => True) m

variable {α β : Type}

lemma extraTo_pure {R : α → Prop} {a : α} (h : R a) : ExtraTo R (Pure.pure a : SirM α) :=
  Skip.pure h

lemma allExtra_pure (a : α) : AllExtra (Pure.pure a : SirM α) := extraTo_pure trivial

lemma extraTo_bind {P : α → Prop} {R : β → Prop} {m : SirM α} {g : α → SirM β}
    (hm : ExtraTo P m) (hg : ∀ a, P a → ExtraTo R (g a)) : ExtraTo R (m >>= g) :=
  Skip.congr rfl (by rw [observe_bind, observe_pure]; rfl)
    (Skip.bind (g₂ := fun _ => CoFree.pure ⟨⟩) hm (fun a _ h => hg a h) nofun)

lemma allExtra_perform (op : EvalE.Op) (h : DeadExtra op) :
    AllExtra (CoFree.perform (E := EvalE) (N := .none) op) :=
  Skip.extra (observe_perform op) h fun _ => Skip.pure trivial

lemma allExtra_ub (u : UB) : AllExtra (ub u : SirM α) := by
  unfold ub
  exact extraTo_bind (allExtra_perform (.inr (.ub u)) trivial) fun a _ => nomatch a

lemma allExtra_host (op : HostOp) (h : HostRead op) :
    AllExtra ((Host.host op).mapOps ⟨Sum.inl, fun _ r => r⟩ .id : SirM (HostE.Resp op)) := by
  refine Skip.extra (op := (Sum.inl op : EvalE.Op)) (by rw [observe_mapOps]; rfl)
    (show DeadExtra (Sum.inl op) from h) fun r => ?_
  exact Skip.congr (by rw [observe_mapOps]; rfl) rfl (Skip.pure trivial)

lemma allExtra_read (o n : Word) : AllExtra (mem.read o n) :=
  allExtra_perform (.inr (.read o n)) trivial

lemma allExtra_map {f : α → β} {m : SirM α} (h : AllExtra m) : AllExtra (f <$> m) :=
  extraTo_bind h fun _ _ => allExtra_pure _

lemma allExtra_code (ctx : Context) : AllExtra ctx.code := by
  unfold Context.code
  split
  · exact allExtra_pure _
  · dsimp only
    split
    · exact allExtra_pure _
    · exact allExtra_ub _

lemma allExtra_ite {c : Prop} [Decidable c] {t e : SirM α} (ht : AllExtra t) (he : AllExtra e) :
    AllExtra (if c then t else e) := by
  split
  · exact ht
  · exact he

lemma allExtra_deployed (ctx : Context) : AllExtra ctx.deployedCode := by
  unfold Context.deployedCode
  split
  · exact allExtra_pure _
  · exact allExtra_code ctx

lemma allExtra_eval (ctx : Context) (e : Expr Word) (h : e.isRemovable) :
    AllExtra (e.eval ctx) := by
  cases e <;> (try simp only [Expr.isRemovable, Bool.false_eq_true] at h) <;> simp only [Expr.eval]
  case query q =>
    cases q <;> (try simp only [Bool.false_eq_true] at h) <;> simp only [Query.eval]
    all_goals first | exact allExtra_pure _ | exact allExtra_host _ trivial
  case extcodehash a =>
    exact allExtra_ite (extraTo_bind (allExtra_deployed ctx) fun _ _ => allExtra_pure _)
      (allExtra_host (.extcodehash _) trivial)
  case extcodesize a =>
    exact allExtra_ite (extraTo_bind (allExtra_deployed ctx) fun _ _ => allExtra_pure _)
      (extraTo_bind (allExtra_host (.extcode _) trivial) fun _ _ => allExtra_pure _)
  case codesize => exact extraTo_bind (allExtra_code ctx) fun _ _ => allExtra_pure _
  case returndatasize => exact allExtra_map (allExtra_host .returndata trivial)
  case keccak256 => exact allExtra_map (allExtra_read _ _)
  case mload => exact allExtra_map (allExtra_read _ _)
  case balance => exact allExtra_host (.balance _) trivial
  case sload => exact allExtra_host (.sload _) trivial
  case tload => exact allExtra_host (.tload _) trivial
  case dataOffset d =>
    unfold Context.getDataOffset
    dsimp only
    split
    · refine extraTo_bind (allExtra_pure _) fun _ _ => ?_
      split
      · exact allExtra_pure _
      · split
        · exact allExtra_pure _
        · exact allExtra_ub _
    · refine extraTo_bind (allExtra_ub _) fun _ _ => ?_
      split
      · exact allExtra_pure _
      · split
        · exact allExtra_pure _
        · exact allExtra_ub _
  case malloc => exact allExtra_perform (.inr (.alloc .zeroed _)) trivial
  case mallocany => exact allExtra_perform (.inr (.alloc .uninitialized _)) trivial
  case mainStartOffset | initEndOffset =>
    exact allExtra_ite (allExtra_pure _) (extraTo_bind (allExtra_ub _) fun _ _ => allExtra_pure _)
  case getImmutable i =>
    unfold Context.getImmutable
    dsimp only
    split
    all_goals
      refine extraTo_bind (P := fun _ => True) (by first | exact allExtra_ub _ | exact allExtra_pure _)
        fun _ _ => ?_
      split
      · split
        · split
          · exact allExtra_pure _
          · exact extraTo_bind (allExtra_ub _) fun _ _ => allExtra_pure _
        · exact allExtra_ub _
      · exact allExtra_ub _
  all_goals exact allExtra_pure _

end Extra

section Lift

abbrev RecE := Effect.Rec CallI CallO EvalE

abbrev RExtra : RecE.Op → Prop := recExtra DeadExtra

variable {α β γ δ : Type}

lemma skip_lift {bad : α → Prop} {Ret : α → β → Prop} {m₁ : SirM α} {m₂ : SirM β}
    (h : Skip DeadExtra bad Ret m₁ m₂) :
    Skip RExtra bad Ret (m₁.mapOps ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none α)
      (m₂.mapOps ⟨Sum.inr, fun _ r => r⟩ .id) :=
  Skip.mapOps _ _ (fun _ h => h) h

lemma rextraTo_lift {P : α → Prop} {m : SirM α} (h : ExtraTo P m) :
    Skip RExtra (fun _ => False) (fun a (_ : PUnit) => P a)
      (m.mapOps ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none α) (CoFree.pure ⟨⟩) :=
  Skip.congr rfl (by rw [observe_mapOps, observe_pure]; rfl) (skip_lift h)

lemma skip_refl {Ret : α → α → Prop} (hRet : ∀ a, Ret a a) (m : CoFree RecE .none α) :
    Skip RExtra (fun _ => False) Ret m m :=
  Skip.of_bisim (Bisim.refl hRet m)

lemma skip_refl_bind {Ret : γ → δ → Prop} (m : CoFree RecE .none α)
    {g₁ : α → CoFree RecE .none γ} {g₂ : α → CoFree RecE .none δ}
    (hg : ∀ a, Skip RExtra (fun _ => False) Ret (g₁ a) (g₂ a)) :
    Skip RExtra (fun _ => False) Ret (m >>= g₁) (m >>= g₂) :=
  Skip.bind (skip_refl (fun _ => rfl) m) (fun a _ h => h ▸ hg a) nofun

end Lift

section Vars

lemma allExtra_lookup (vars : Vars) (v : VarId) : AllExtra (vars.lookup v) := by
  unfold Vars.lookup
  split
  · exact allExtra_pure _
  · exact allExtra_ub _

lemma extraTo_resolve (e : Expr VarId) (h : e.isRemovable) {l : VarId → SirM Word}
    (hl : ∀ v, AllExtra (l v)) : ExtraTo (fun e' : Expr Word => e'.isRemovable = true) (e.resolve l) := by
  cases e <;> (try simp only [Expr.isRemovable, Bool.false_eq_true] at h) <;> simp only [Expr.resolve]
  case query q => cases q <;> first | exact extraTo_pure rfl | simp at h
  all_goals repeat (first
    | exact extraTo_pure rfl
    | refine extraTo_bind (hl _) fun _ _ => ?_)

lemma agree_assign {d : Array Bool} {v₁ v₂ : Vars} (h : VarsAgree d v₁ v₂) (xs : Array (VarId × Word)) :
    VarsAgree d (xs.foldl (fun l (x : VarId × Word) => match x with | (v, w) => l.insert v w) v₁)
      (xs.foldl (fun l (x : VarId × Word) => match x with | (v, w) => l.insert v w) v₂) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  generalize xs.toList = L
  induction L generalizing v₁ v₂ with
  | nil => exact h
  | cons x L ih => exact ih (agree_insert h x.1 x.2)

lemma skip_assignAll {d : Array Bool} {v₁ v₂ : Vars} (h : VarsAgree d v₁ v₂) (vs : Array VarId)
    (ws : Array Word) :
    Skip DeadExtra (fun _ => False) (VarsAgree d) (v₁.assignAll vs ws) (v₂.assignAll vs ws) := by
  unfold Vars.assignAll
  dsimp only
  split
  · exact Skip.pure (agree_assign h _)
  · exact Skip.bind (Skip.of_bisim (Bisim.refl (fun _ => rfl) _))
      (fun _ _ _ => Skip.pure (agree_assign h _)) fun _ (h : False) => h.elim

end Vars

section EvalFn

lemma program_getElem? (p : Program) (f : FunctionId) :
    p.removeUnusedLets[f]? = p[f]?.map Function.removeUnusedLets :=
  Array.getElem?_map ..

def keepBlock (d : Array Bool) (blk : Block) : Block :=
  { blk with ops := blk.ops.filter (!·.isDeadLet d) }

lemma function_getElem? (fn : Function) (b : BlockId) :
    fn.removeUnusedLets[b]? = fn[b]?.map (keepBlock fn.deadVars) :=
  Array.getElem?_map ..

lemma mem_flatOps {fn : Function} {blk : Block} {op : Operation VarId} (hb : blk ∈ fn.blocks)
    (ho : op ∈ blk.ops) : op ∈ flatOps fn :=
  List.mem_flatMap.2 ⟨blk, Array.mem_toList_iff.2 hb, Array.mem_toList_iff.2 ho⟩

lemma mem_extraReads {fn : Function} {blk : Block} {x : VarId} (hb : blk ∈ fn.blocks)
    (hx : x ∈ blk.control.reads ++ blk.outputs.toList) : x ∈ extraReads fn :=
  List.mem_flatMap.2 ⟨blk, Array.mem_toList_iff.2 hb, hx⟩

lemma deadLet_inv {d : Array Bool} {op : Operation VarId} (h : op.isDeadLet d = true) :
    ∃ out e, op = .let out e ∧ e.isRemovable = true ∧ Dead d out := by
  unfold Operation.isDeadLet at h
  cases op with
  | «let» out e =>
    cases hr : e.isRemovable
    · simp [Operation.removableLet?, hr] at h
    · simp only [Operation.removableLet?, hr, ↓reduceIte] at h
      exact ⟨out, e, rfl, hr, by unfold Dead; simpa using h⟩
  | _ => cases h

def StateRel (d : Array Bool) (s₁ s₂ : Option CallO × Array Word × BlockId × Vars) : Prop :=
  s₁.1 = s₂.1 ∧ s₁.2.1 = s₂.2.1 ∧ s₁.2.2.1 = s₂.2.2.1 ∧ VarsAgree d s₁.2.2.2 s₂.2.2.2

variable {ctx ctx' : Context}

lemma skip_evalFn (hp : ctx'.program = ctx.program.removeUnusedLets)
    (hexpr : ∀ e, Expr.eval ctx' e = Expr.eval ctx e)
    (hstmt : ∀ s, Stmt.exec ctx' s = Stmt.exec ctx s)
    (hcs : ctx'.checkStateful = ctx.checkStateful) (i : CallI) :
    Skip DeadExtra (fun _ => False) Eq (evalFn ctx i) (evalFn ctx' i) := by
  unfold evalFn
  refine Skip.fix (fun x => ?_) i
  obtain ⟨f, a⟩ := x
  have hfn' : ctx'.program[f]? = ctx.program[f]?.map Function.removeUnusedLets := by
    rw [hp]; exact program_getElem? _ _
  dsimp only
  rw [hfn']
  cases ctx.program[f]? with
  | none => exact skip_refl (fun _ => rfl) _
  | some fn =>
    dsimp only
    obtain ⟨hops, hctl⟩ := deadVars_sound fn
    refine Skip.bind (Ret := fun (s₁ s₂ : Option CallO × Array Word × BlockId × Vars) =>
        s₁.1 = s₂.1) (Skip.loop (StateRel fn.deadVars) (fun b₁ b₂ hb => ?_)
        ⟨rfl, rfl, rfl, fun _ _ => rfl⟩) (fun s₁ s₂ h => ?_) fun _ (h : False) => h.elim
    rotate_left
    · obtain ⟨o₁, _⟩ := s₁
      obtain ⟨o₂, _⟩ := s₂
      dsimp only at h ⊢
      subst h
      exact skip_refl (fun _ => rfl) _
    obtain ⟨o, inp, bi, v₁⟩ := b₁
    obtain ⟨o', inp', bi', v₂⟩ := b₂
    obtain ⟨rfl, rfl, rfl, hv⟩ := hb
    dsimp only
    rw [function_getElem?]
    cases hblk : fn[bi]? with
    | none =>
      exact skip_refl_bind _ fun _ => Skip.pure ⟨rfl, rfl, rfl, hv⟩
    | some blk =>
      dsimp only [keepBlock]
      have hb : blk ∈ fn.blocks := Array.mem_of_getElem? hblk
      refine Skip.bind (skip_lift (skip_assignAll hv blk.inputs inp)) (fun w₁ w₂ hw => ?_)
        fun _ (h : False) => h.elim
      refine Skip.bind (Skip.forIn_array_filter (VarsAgree fn.deadVars)
        (!·.isDeadLet fn.deadVars) blk.ops (fun op hop hk v₁ v₂ hv => ?_)
        (fun op hop hk v₁ v₂ hv => ?_) hw) (fun w₁ w₂ hw => ?_) fun _ (h : False) => h.elim
      · have hd : op.isDeadLet fn.deadVars = false := by simpa using hk
        have hr : ∀ x ∈ op.reads, ¬Dead fn.deadVars x :=
          fun x hx => hops op (mem_flatOps hb hop) hd x hx
        rw [op_resolve_congr hv op hr]
        refine skip_refl_bind _ fun o => ?_
        cases o with
        | «let» out e =>
          dsimp only
          rw [hexpr]
          exact skip_refl_bind _ fun val => Skip.pure (agree_insert hv out val)
        | stmt st =>
          dsimp only
          rw [hstmt]
          exact skip_refl_bind _ fun _ => Skip.pure hv
        | icall g args outs =>
          exact skip_refl_bind _ fun res => Skip.bind (skip_lift (skip_assignAll hv outs res))
            (fun _ _ h => Skip.pure h) fun _ (h : False) => h.elim
      · have hd : op.isDeadLet fn.deadVars = true := by simpa using hk
        obtain ⟨out, e, rfl, hrem, hdead⟩ := deadLet_inv hd
        refine Skip.prefix (P := fun o => ∃ e', o = Operation.let out e' ∧ e'.isRemovable = true)
          (rextraTo_lift ?_) fun o ho => ?_
        · exact extraTo_bind (extraTo_resolve e hrem (allExtra_lookup v₁))
            fun e' h => extraTo_pure ⟨e', rfl, h⟩
        · obtain ⟨e', rfl, hrem'⟩ := ho
          exact Skip.prefix (rextraTo_lift (allExtra_eval ctx e' hrem')) fun val _ =>
            Skip.pure (agree_insert_dead hv hdead val)
      · have hc : ∀ x ∈ blk.control.reads, ¬Dead fn.deadVars x :=
          fun x hx => hctl x (mem_extraReads hb (List.mem_append_left _ hx))
        have ho : ∀ x ∈ blk.outputs, ¬Dead fn.deadVars x := fun x hx =>
          hctl x (mem_extraReads hb (List.mem_append_right _ (Array.mem_toList_iff.2 hx)))
        rw [ctrl_resolve_congr hw _ hc, lookupAll_eq hw ho]
        refine skip_refl_bind _ fun c => ?_
        have hret : fn.removeUnusedLets.returns = fn.returns := rfl
        cases c <;> dsimp only <;> (try rw [hret]) <;> (try rw [hcs])
        all_goals repeat (first
          | exact Skip.pure ⟨rfl, rfl, rfl, hw⟩
          | exact Skip.pure rfl
          | (refine skip_refl_bind _ fun _ => ?_)
          | split)

lemma skip_runInner (hp : ctx'.program = ctx.program.removeUnusedLets)
    (hexpr : ∀ e, Expr.eval ctx' e = Expr.eval ctx e)
    (hstmt : ∀ s, Stmt.exec ctx' s = Stmt.exec ctx s)
    (hcs : ctx'.checkStateful = ctx.checkStateful) (hk : ctx'.mode.kind = ctx.mode.kind) :
    Skip DeadExtra (fun _ => False) Eq (runInner ctx) (runInner ctx') := by
  unfold runInner
  dsimp only
  rw [hk, hp]
  cases ctx.mode.kind <;> dsimp only <;>
    exact Skip.bind (skip_evalFn hp hexpr hstmt hcs _)
      (fun _ _ _ => Skip.of_bisim (Bisim.refl (fun _ => rfl) _)) fun _ (h : False) => h.elim

end EvalFn

section Run

def layoutBack {p : Program} (l : Layout p.removeUnusedLets) : Layout p :=
  ⟨l.init, l.init_u32, l.main, l.main_u32, l.mainStartOffset, l.initDataOffsets, l.mainDataOffsets,
   l.immutableOffsets, l.atLeastOne_immOffsets, l.no_imm_imm_overlap, l.no_imm_data_overlap⟩

def layoutFwd {p : Program} (l : Layout p) : Layout p.removeUnusedLets :=
  ⟨l.init, l.init_u32, l.main, l.main_u32, l.mainStartOffset, l.initDataOffsets, l.mainDataOffsets,
   l.immutableOffsets, l.atLeastOne_immOffsets, l.no_imm_imm_overlap, l.no_imm_data_overlap⟩

variable (p : Program) (l : Layout p.removeUnusedLets) {N N' : NonDeterminism} {α α' : Type}

lemma same_runInit {Ret : α → UB ⊕ InitOutcome → Prop} {R' : α' → UB ⊕ InitOutcome → Prop}
    (x : CoFree WorldE N α) {x' : CoFree WorldE N' α'} (c : ByteArray) (e : Env) (w₀ : World)
    (hw : Same R' x' (p.runInit (layoutBack l) c e w₀)) (hR : ∀ a b, R' a b → ¬b.isLeft = true)
    (h : Same Ret x (p.runInit (layoutBack l) c e w₀)) : Same Ret x (p.removeUnusedLets.runInit l c e w₀) := by
  have hnb := Same.noBad hw hR
  unfold Program.runInit Program.run at *
  refine Same.removeDeadAllocs _ (fun _ => rfl) x e.address w₀ (skip_runInner ?_ ?_ ?_ ?_ ?_) hnb h
  · rfl
  · intro ex; cases ex <;> rfl
  · intro st; cases st <;> rfl
  · rfl
  · rfl

lemma same_runMain {Ret : α → UB ⊕ Outcome → Prop} {R' : α' → UB ⊕ Outcome → Prop}
    (x : CoFree WorldE N α) {x' : CoFree WorldE N' α'} (imms : MainImmutables) (static : Bool)
    (cd : BytesX32) (e : Env) (w₀ : World)
    (hw : Same R' x' (p.runMain (layoutBack l) imms static cd e w₀)) (hR : ∀ a b, R' a b → ¬b.isLeft = true)
    (h : Same Ret x (p.runMain (layoutBack l) imms static cd e w₀)) :
    Same Ret x (p.removeUnusedLets.runMain l imms static cd e w₀) := by
  rw [← Same.bind_pure_right_iff] at hw h ⊢
  have hnb := Same.noBad hw hR
  unfold Program.runMain Program.run at *
  refine Same.removeDeadAllocs id (fun _ => rfl) x e.address w₀ (skip_runInner ?_ ?_ ?_ ?_ ?_) hnb h
  · rfl
  · intro ex; cases ex <;> rfl
  · intro st; cases st <;> rfl
  · rfl
  · rfl

end Run

section Semantics

variable {p : Program}

lemma definedAnd_right {α : Type} {R : α → α → Prop} (a b : UB ⊕ α) (h : DefinedAnd R a b) :
    ¬b.isLeft = true := by
  rcases a with _ | _ <;> rcases b with _ | _ <;> simp [DefinedAnd] at h ⊢

lemma removeUnusedLets_equiv (hs : Safe p) : Equiv p p.removeUnusedLets := by
  obtain ⟨⟨⟨l⟩, _, H⟩, _⟩ := hs
  refine ⟨⟨l⟩, ⟨layoutFwd l⟩, fun l₁ l₂ e c w₀ hu => ?_⟩
  have h₁ := H l₁ (layoutBack l₂) e c w₀ hu
  refine Same.mono (fun a b hab => ?_) (same_runInit p l₂ _ c e w₀ h₁ definedAnd_right h₁)
  rcases a with _ | ⟨m₁, s₁⟩ | _ | _ | _ <;> rcases b with _ | ⟨m₂, s₂⟩ | _ | _ | _ <;>
    simp only [DefinedAnd, DeployOutcomeEquiv] at hab ⊢ <;> try exact hab
  exact ⟨hab.1, fun static cd e' w => same_runMain p l₂ _ m₂ static cd e' w (hab.2 static cd e' w)
    definedAnd_right (hab.2 static cd e' w)⟩

lemma removeUnusedLets_safe (hs : Safe p) : Safe p.removeUnusedLets := by
  refine ⟨(removeUnusedLets_equiv hs).symm.refl_left, fun l e c w₀ hu => ?_⟩
  obtain ⟨hdet, hret⟩ := hs.2 (layoutBack l) e c w₀ hu
  have hself := hs.1.2.2 (layoutBack l) (layoutBack l) e c w₀ hu
  have hyz := same_runInit p l _ c e w₀ hself definedAnd_right hdet
  refine ⟨same_runInit p l _ c e w₀ hself definedAnd_right (Same.symm_eq hyz), fun imms w' ho => ?_⟩
  obtain ⟨_, hoy, rfl⟩ := Same.hasOutcome_left hyz ho
  obtain ⟨hwf, hms⟩ := hret imms w' hoy
  obtain ⟨a, hab⟩ := Same.hasOutcome_right hself hoy
  rcases a with _ | ⟨m₁, s₁⟩ | _ | _ | _ <;>
    simp only [DefinedAnd, DeployOutcomeEquiv, reduceCtorEq] at hab
  refine ⟨hwf, fun e' static cd w => ?_⟩
  have hw := hab.2 static cd e' w
  have hyz' := same_runMain p l _ imms static cd e' w hw definedAnd_right (hms e' static cd w)
  exact same_runMain p l _ imms static cd e' w hw definedAnd_right (Same.symm_eq hyz')

end Semantics

section WF

variable {p : Program}

def OpsOk : List VarId → List (Operation VarId) → Prop
  | _, [] => True
  | pre, op :: l => (∀ v ∈ op.reads, v ∈ pre) ∧ OpsOk (pre ++ op.defs) l

lemma opsOk_iff : ∀ (l : List (Operation VarId)) (pre : List VarId),
    OpsOk pre l ↔ ∀ i (h : i < l.length), ∀ v ∈ l[i].reads, v ∈ pre ++ (l.take i).flatMap Operation.defs
  | [], _ => by simp [OpsOk]
  | op :: l, pre => by
    rw [OpsOk, opsOk_iff l]
    constructor
    · rintro ⟨h₀, h⟩ i hi v hv
      cases i with
      | zero => simpa using h₀ v hv
      | succ i =>
        have := h i (by simpa using hi) v hv
        simpa [List.flatMap_cons, List.append_assoc] using this
    · intro h
      refine ⟨fun v hv => by simpa using h 0 (by simp) v hv, fun i hi v hv => ?_⟩
      have := h (i + 1) (by simpa using hi) v hv
      simpa [List.flatMap_cons, List.append_assoc] using this

lemma deadLet_defs {d : Array Bool} {op : Operation VarId} (h : op.isDeadLet d = true) :
    ∀ x ∈ op.defs, Dead d x := by
  obtain ⟨out, e, rfl, _, hd⟩ := deadLet_inv h
  intro x hx
  simp only [Operation.defs, List.mem_singleton] at hx
  exact hx ▸ hd

lemma mem_flatMap_filter {d : Array Bool} {x : VarId} (hx : ¬Dead d x) :
    ∀ l : List (Operation VarId), x ∈ l.flatMap Operation.defs →
      x ∈ (l.filter (!·.isDeadLet d)).flatMap Operation.defs
  | [], h => h
  | op :: l, h => by
    rw [List.filter_cons]
    rw [List.flatMap_cons, List.mem_append] at h
    cases hk : op.isDeadLet d
    · simp only [Bool.not_false, ↓reduceIte, List.flatMap_cons, List.mem_append]
      exact h.imp id (mem_flatMap_filter hx l)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases h with h | h
      · exact (hx (deadLet_defs hk x h)).elim
      · exact mem_flatMap_filter hx l h

lemma opsOk_filter {d : Array Bool} : ∀ (l : List (Operation VarId)) (pre pre' : List VarId),
    (∀ op ∈ l, op.isDeadLet d = false → ∀ x ∈ op.reads, ¬Dead d x) →
    (∀ x, ¬Dead d x → x ∈ pre → x ∈ pre') →
    OpsOk pre l → OpsOk pre' (l.filter (!·.isDeadLet d))
  | [], _, _, _, _, h => h
  | op :: l, pre, pre', hr, hpre, ⟨h₀, h⟩ => by
    rw [List.filter_cons]
    cases hk : op.isDeadLet d
    · refine ⟨fun v hv => hpre v (hr op (.head _) hk v hv) (h₀ v hv), ?_⟩
      refine opsOk_filter l _ _ (fun o ho => hr o (.tail _ ho)) (fun x hx hm => ?_) h
      rcases List.mem_append.1 hm with hm | hm
      · exact List.mem_append_left _ (hpre x hx hm)
      · exact List.mem_append_right _ hm
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine opsOk_filter l _ _ (fun o ho => hr o (.tail _ ho)) (fun x hx hm => ?_) h
      rcases List.mem_append.1 hm with hm | hm
      · exact hpre x hx hm
      · exact (hx (deadLet_defs hk x hm)).elim

lemma keepBlock_ops (d : Array Bool) (b : Block) :
    (keepBlock d b).ops.toList = b.ops.toList.filter (!·.isDeadLet d) :=
  Array.toList_filter ..

lemma mem_block_defs {d : Array Bool} {b : Block} {x : VarId} (hx : ¬Dead d x) (h : x ∈ b.defs) :
    x ∈ (keepBlock d b).defs := by
  unfold Block.defs at h ⊢
  rw [keepBlock_ops]
  rcases List.mem_append.1 h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (mem_flatMap_filter hx _ h)

lemma mem_prev_defs {d : Array Bool} {x : VarId} (hx : ¬Dead d x) :
    ∀ prev : List Block, x ∈ prev.flatMap Block.defs →
      x ∈ (prev.map (keepBlock d)).flatMap Block.defs := by
  intro prev h
  obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.1 h
  exact List.mem_flatMap.2 ⟨_, List.mem_map_of_mem hb, mem_block_defs hx hxb⟩

lemma flatMap_filter_sublist (d : Array Bool) :
    ∀ l : List (Operation VarId),
      ((l.filter (!·.isDeadLet d)).flatMap Operation.defs).Sublist (l.flatMap Operation.defs)
  | [] => .slnil
  | op :: l => by
    rw [List.filter_cons, List.flatMap_cons]
    split
    · rw [List.flatMap_cons]
      exact (flatMap_filter_sublist d l).append_left _
    · exact (flatMap_filter_sublist d l).trans (List.sublist_append_right _ _)

lemma block_defs_sublist (d : Array Bool) (b : Block) : (keepBlock d b).defs.Sublist b.defs := by
  unfold Block.defs
  rw [keepBlock_ops]
  exact (flatMap_filter_sublist d _).append_left _

lemma function_defs_sublist (fn : Function) : fn.removeUnusedLets.defs.Sublist fn.defs := by
  unfold Function.defs
  show ((fn.blocks.map (keepBlock fn.deadVars)).toList.flatMap Block.defs).Sublist _
  rw [Array.toList_map, List.flatMap_map]
  generalize fn.blocks.toList = L
  induction L with
  | nil => exact .slnil
  | cons b L ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (block_defs_sublist _ b).append ih

lemma pathTo_back {fn : Function} {prev' : List Block} {b : BlockId}
    (h : fn.removeUnusedLets.PathTo prev' b) :
    ∃ prev, fn.PathTo prev b ∧ prev' = prev.map (keepBlock fn.deadVars) := by
  induction h with
  | entry => exact ⟨[], .entry, rfl⟩
  | step _ hb' ht' ih =>
    obtain ⟨prev, hp, rfl⟩ := ih
    rw [function_getElem?, Option.map_eq_some_iff] at hb'
    obtain ⟨blk, hb, rfl⟩ := hb'
    exact ⟨prev ++ [blk], .step hp hb ht', by simp⟩

lemma mem_blocks {fn : Function} {b' : Block} (h : b' ∈ fn.removeUnusedLets.blocks) :
    ∃ b ∈ fn.blocks, b' = keepBlock fn.deadVars b := by
  obtain ⟨b, hb, rfl⟩ := Array.mem_map.1 h
  exact ⟨b, hb, rfl⟩

lemma mem_ops {d : Array Bool} {b : Block} {op : Operation VarId} (h : op ∈ (keepBlock d b).ops) :
    op ∈ b.ops :=
  (Array.mem_filter.1 h).1

lemma definedBeforeUse {fn : Function} {b : Block} (hb : b ∈ fn.blocks) {pre : List VarId}
    {pre' : List VarId} (hpre : ∀ x, ¬Dead fn.deadVars x → x ∈ pre → x ∈ pre')
    (h : b.DefinedBeforeUse pre) : (keepBlock fn.deadVars b).DefinedBeforeUse pre' := by
  obtain ⟨hops, hctl⟩ := deadVars_sound fn
  obtain ⟨hbo, hbc⟩ := h
  have hok : OpsOk (pre ++ b.inputs.toList) b.ops.toList := by
    rw [opsOk_iff]
    intro i hi v hv
    have := hbo i (by simpa using hi) v (by simpa using hv)
    simpa [Block.definedBefore, List.append_assoc] using this
  have hok' := opsOk_filter (d := fn.deadVars) _ _ (pre' ++ b.inputs.toList)
    (fun op ho hk x hx => hops op (mem_flatOps hb (Array.mem_toList_iff.1 ho)) hk x hx)
    (fun x hx hm => by
      rcases List.mem_append.1 hm with hm | hm
      · exact List.mem_append_left _ (hpre x hx hm)
      · exact List.mem_append_right _ hm) hok
  rw [← keepBlock_ops, opsOk_iff] at hok'
  refine ⟨fun i hi v hv => ?_, fun v hv => ?_⟩
  · have := hok' i (by simpa using hi) v (by simpa using hv)
    simpa [Block.definedBefore, keepBlock, List.append_assoc] using this
  · have hd : ¬Dead fn.deadVars v := hctl v (mem_extraReads hb hv)
    have := hbc v hv
    simp only [Block.definedBefore] at this ⊢
    rw [List.take_of_length_le (by simp)] at this ⊢
    rcases List.mem_append.1 this with h | h
    · exact List.mem_append_left _ (hpre v hd h)
    · show v ∈ pre' ++ (keepBlock fn.deadVars b).defs
      exact List.mem_append_right _ (mem_block_defs hd h)

lemma function_wf {fn : Function} (hwf : fn.WF) : fn.removeUnusedLets.WF where
  entry_valid := by
    simpa [Function.ValidBlockId, Function.removeUnusedLets] using hwf.entry_valid
  ssa := (function_defs_sublist fn).nodup hwf.ssa
  definedBeforeUse prev' b blk' hp' hb' := by
    obtain ⟨prev, hp, rfl⟩ := pathTo_back hp'
    rw [function_getElem?, Option.map_eq_some_iff] at hb'
    obtain ⟨blk, hb, rfl⟩ := hb'
    exact definedBeforeUse (Array.mem_of_getElem? hb) (fun x hx hm => mem_prev_defs hx prev hm)
      (hwf.definedBeforeUse prev b blk hp hb)
  validTargets b' hb' t ht := by
    obtain ⟨b, hb, rfl⟩ := mem_blocks hb'
    obtain ⟨tb, htb, hsz⟩ := hwf.validTargets b hb t ht
    exact ⟨keepBlock fn.deadVars tb, by rw [function_getElem?, htb]; rfl, hsz⟩
  iretArity b' hb' hc := by
    obtain ⟨b, hb, rfl⟩ := mem_blocks hb'
    exact hwf.iretArity b hb hc

lemma callee_map {g : FunctionId} {n : Nat} {ret : ReturnKind} (h : p.Callee g n ret) :
    p.removeUnusedLets.Callee g n ret := by
  obtain ⟨fn, hg, hret, e, he, hin⟩ := h
  refine ⟨fn.removeUnusedLets, by rw [program_getElem?, hg]; rfl, hret,
    keepBlock fn.deadVars e, ?_, hin⟩
  rw [function_getElem?]
  show Option.map (keepBlock fn.deadVars) fn[fn.entry]? = _
  rw [he]
  rfl

lemma calls_back {d : Array Bool} {b : Block} {g : FunctionId} (h : (keepBlock d b).Calls g) :
    b.Calls g := by
  rcases h with ⟨op, hop, hc⟩ | hc
  · exact .inl ⟨op, mem_ops hop, hc⟩
  · exact .inr hc

lemma callEdge_back {f g : FunctionId} (h : p.removeUnusedLets.CallEdge f g) : p.CallEdge f g := by
  obtain ⟨fn', hfn', prev', b, blk', hp', hb', hc'⟩ := h
  rw [program_getElem?, Option.map_eq_some_iff] at hfn'
  obtain ⟨fn, hfn, rfl⟩ := hfn'
  obtain ⟨prev, hp, rfl⟩ := pathTo_back hp'
  rw [function_getElem?, Option.map_eq_some_iff] at hb'
  obtain ⟨blk, hb, rfl⟩ := hb'
  exact ⟨fn, hfn, prev, b, blk, hp, hb, calls_back hc'⟩

lemma reachable_back {r f : FunctionId} (h : p.removeUnusedLets.Reachable r f) : p.Reachable r f := by
  induction h with
  | root => exact .root
  | call _ he ih => exact .call ih (callEdge_back he)

lemma transGen_back {a b : FunctionId} (h : Relation.TransGen p.removeUnusedLets.CallEdge a b) :
    Relation.TransGen p.CallEdge a b := by
  induction h with
  | single he => exact .single (callEdge_back he)
  | tail _ he ih => exact .tail ih (callEdge_back he)

lemma validFrom {k : ExecutionModeKind} {r : FunctionId} (h : p.ValidFrom k r) :
    p.removeUnusedLets.ValidFrom k r := by
  intro f fn' hr hf' prev' b blk' hp' hb' op hop
  rw [program_getElem?, Option.map_eq_some_iff] at hf'
  obtain ⟨fn, hfn, rfl⟩ := hf'
  obtain ⟨prev, hp, rfl⟩ := pathTo_back hp'
  rw [function_getElem?, Option.map_eq_some_iff] at hb'
  obtain ⟨blk, hb, rfl⟩ := hb'
  have := h f fn (reachable_back hr) hfn prev b blk hp hb op (mem_ops hop)
  cases op <;> exact this

lemma removeUnusedLets_wf (hwf : p.WF) : p.removeUnusedLets.WF where
  functions fn' hfn' := by
    obtain ⟨fn, hfn, rfl⟩ := Array.mem_map.1 hfn'
    exact function_wf (hwf.functions fn hfn)
  validCalls fn' hfn' b' hb' := by
    obtain ⟨fn, hfn, rfl⟩ := Array.mem_map.1 hfn'
    obtain ⟨b, hb, rfl⟩ := mem_blocks hb'
    have hv := hwf.validCalls fn hfn b hb
    refine ⟨fun op hop => ?_, ?_⟩
    · have := hv.1 op (mem_ops hop)
      cases op with
      | icall g ins outs => exact callee_map this
      | _ => trivial
    · have := hv.2
      simp only [keepBlock]
      cases h : b.control with
      | icallNever g ins => rw [h] at this; exact callee_map this
      | _ => trivial
  initEntry := callee_map hwf.initEntry
  mainEntry := callee_map hwf.mainEntry
  initOps := validFrom hwf.initOps
  mainOps := validFrom hwf.mainOps
  acyclicCalls f h := hwf.acyclicCalls f (transGen_back h)

end WF

end Sir.Proofs.RemoveUnusedLets
