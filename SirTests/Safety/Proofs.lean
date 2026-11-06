import SirTests.Safety.Defs
import SirTests.KernelRfl
import ITree.Step.Theorems
import Sir.Safety
import Sir.Layout.Theorems
import ITree.Machine.Theorems

namespace SirTests.Safety

open Sir Host CoFree

universe u

inductive Halts {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u} (op : E.Op) :
    CoFree E N A → Prop
  | now {m : CoFree E N A} {k : E.Resp op → CoFree E N A} : m.observe = .impure op k → Halts op m
  | silent {m m' : CoFree E N A} : m.observe = .silent m' → Halts op m' → Halts op m
  | branch {m : CoFree E N A} {c : N.Op} {k : N.Resp c → CoFree E N A} :
      m.observe = .branch c k → (∀ r, Halts op (k r)) → Halts op m

inductive Returns {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u} (a : A) :
    CoFree E N A → Prop
  | now {m : CoFree E N A} : m.observe = .pure a → Returns a m
  | silent {m m' : CoFree E N A} : m.observe = .silent m' → Returns a m' → Returns a m
  | branch {m : CoFree E N A} {c : N.Op} {k : N.Resp c → CoFree E N A} :
      m.observe = .branch c k → (∀ r, Returns a (k r)) → Returns a m

section Returns

variable {E : Effect.{u}} {N N₁ N₂ : NonDeterminism.{u}} {A : Type u} {a : A}

lemma Returns.same {B : Type u} {b : B} {R : A → B → Prop} {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h₁ : Returns a m₁) (h₂ : Returns b m₂) (hr : R a b) : Same R m₁ m₂ := by
  refine ⟨fun x y => Returns a x ∧ Returns b y, ⟨h₁, h₂⟩, fun x y ⟨hx, hy⟩ => ?_⟩
  induction hx with
  | now hx =>
    induction hy with
    | now hy => exact .ret a b hx hy hr
    | silent hy hy' ih => exact .silentR hy (ih ⟨.now hx, hy'⟩)
    | branch hy hy' ih => exact .branchR _ hy fun r => ih r ⟨.now hx, hy' r⟩
  | silent hx hx' ih => exact .silentL hx (ih ⟨hx', hy⟩)
  | branch hx hx' ih => exact .branchL _ hx fun r => ih r ⟨hx' r, hy⟩

lemma Returns.outcome {m : CoFree E N A} {o : Outcome E A} (h : Returns a m) (ho : HasOutcome m o) :
    o = .res a := by
  induction ho with
  | res hm => cases h <;> simp_all
  | terminal _ hk =>
    obtain ⟨k, hk⟩ := hk
    cases h <;> simp_all
  | silent _ hm ih => cases h <;> simp_all
  | branch _ hm ih =>
    obtain ⟨br, k, hm, r, rfl⟩ := hm
    cases h with
    | now h => rw [hm] at h; cases h
    | silent h => rw [hm] at h; cases h
    | branch h hk => rw [hm] at h; cases h; exact ih (hk r)
  | impure _ hm ih =>
    obtain ⟨op', k, hm, r, rfl⟩ := hm
    cases h with
    | now h => rw [hm] at h; cases h
    | silent h => rw [hm] at h; cases h
    | branch h => rw [hm] at h; cases h

lemma Returns.hasOutcome {m : CoFree E N A} (h : Returns a m) : HasOutcome m (.res a) := by
  induction h with
  | now hm => exact .res hm
  | silent hm _ ih => exact .silent ih hm
  | branch hm _ ih =>
    obtain ⟨r⟩ := N.resp_nonempty _
    exact .branch (ih r) ⟨_, _, hm, r, rfl⟩

lemma Returns.map {B : Type u} {b : B} (f : A → B) {m : CoFree E N A} (h : Returns a m) (hb : f a = b) :
    Returns b (f <$> m) := by
  subst hb
  have e : ∀ m : CoFree E N A, f <$> m = m.bind fun x => CoFree.pure (f x) := fun _ => rfl
  induction h with
  | now hm => exact .now (by rw [e, observe_bind, hm]; rfl)
  | silent hm _ ih => exact .silent (by rw [e, observe_bind, hm]; rfl) ih
  | branch hm _ ih => exact .branch (by rw [e, observe_bind, hm]; rfl) ih

lemma Returns.deterministic {m : CoFree E N A} (h : Returns a m) : Deterministic m :=
  h.same h rfl

lemma Returns.same_inv {B : Type u} {b : B} {R : A → B → Prop} {m₁ : CoFree E N₁ A} {m₂ : CoFree E N₂ B}
    (h : Same R m₁ m₂) (h₁ : Returns a m₁) (h₂ : Returns b m₂) : R a b := by
  induction h₁ with
  | now hx =>
    induction h₂ with
    | now hy => exact h.ret_inv hx hy
    | silent hy _ ih => exact ih (h.silentR_inv hy)
    | branch hy _ ih =>
      obtain ⟨r⟩ := N₂.resp_nonempty _
      exact ih r (h.branchR_inv hy r)
  | silent hx _ ih => exact ih (h.silentL_inv hx)
  | branch hx _ ih =>
    obtain ⟨r⟩ := N₁.resp_nonempty _
    exact ih r (h.branchL_inv hx r)

end Returns

lemma observe_interp {E F : Effect} {N M : NonDeterminism} {A B σ : Type}
    (f : ∀ {X : Type}, σ → Step E N A X → Step F M B (σ × X)) (st : σ) (m : CoFree E N A) :
    (CoFree.interp f st m).observe =
      (f st (m.step m.initial)).map fun p => CoFree.interp f p.1 (m.next p.2) := by
  obtain ⟨S, J, s₀, step, target⟩ := m
  simp only [observe, CoFree.interp, Step.map_map]
  congr 1
  funext ⟨st', s⟩
  rcases s with s | j <;> rfl

lemma Halts.interpHost {self : Address} {o : SimplifiedOutcome} {m : CoFree HostE MemoryND UB}
    (hs : HostState) (hm : Halts (HostOp.halt o) m) :
    Returns (.inr (o.withStore hs.store)) (CoFree.interp (hostStep self) hs m) := by
  induction hm with
  | @now m k h =>
    refine .now ?_
    rw [observe_interp]
    unfold observe at h
    generalize m.step m.initial = y at h ⊢
    cases y <;> cases h
    rfl
  | @silent m m' h _ ih =>
    refine .silent ?_ ih
    rw [observe_interp]
    unfold observe at h
    generalize m.step m.initial = y at h ⊢
    cases y <;> cases h
    rfl
  | @branch m c k h _ ih =>
    refine .branch (k := fun r => CoFree.interp (hostStep self) hs (k r)) ?_ ih
    rw [observe_interp]
    unfold observe at h
    generalize m.step m.initial = y at h ⊢
    cases y <;> cases h
    rfl


def skip {A : Type} : Nat → SirM A → SirM A
  | 0, t => t
  | n + 1, t => match t.observe with
    | .silent t' => skip n t'
    | _ => t

lemma observe_interpMem (mem : MemState) (m : SirM Empty) :
    (CoFree.interp memStep mem m).observe =
      (memStep mem (m.step m.initial)).map fun p => CoFree.interp memStep p.1 (m.next p.2) :=
  observe_interp memStep mem m

lemma observe_interpMem_silent {mem : MemState} {m m' : SirM Empty} (h : m.observe = .silent m') :
    (CoFree.interp memStep mem m).observe = .silent (CoFree.interp memStep mem m') := by
  rw [observe_interpMem]
  unfold observe at h
  generalize m.step m.initial = y at h ⊢
  cases y <;> cases h
  rfl

lemma observe_interpMem_impure {mem : MemState} {m : SirM Empty} {op : EvalE.Op}
    {k : EvalE.Resp op → SirM Empty} (h : m.observe = .impure op k) :
    ∃ k', (∀ r, m.next (k' r) = k r) ∧ (CoFree.interp memStep mem m).observe =
      (memStep mem (.impure op k')).map fun p => CoFree.interp memStep p.1 (m.next p.2) := by
  rw [observe_interpMem]
  unfold observe at h
  generalize m.step m.initial = y at h ⊢
  cases y <;> cases h
  exact ⟨_, fun _ => rfl, rfl⟩

lemma halts_skip {op : HostOp} (n : Nat) {mem : MemState} {t : SirM Empty}
    (h : Halts op (CoFree.interp memStep mem (skip n t))) : Halts op (CoFree.interp memStep mem t) := by
  induction n generalizing t with
  | zero => exact h
  | succ n ih =>
    unfold skip at h
    split at h
    next t' ht => exact .silent (observe_interpMem_silent ht) (ih h)
    next => exact h

def afterAlloc (t : SirM Empty) (w : Word) : SirM Empty :=
  match t.observe with
  | .impure (.inr (.alloc _ _)) k => k w
  | _ => t

def afterWrite (t : SirM Empty) : Unit → SirM Empty :=
  match t.observe with
  | .impure (.inr (.write _ _)) k => k
  | _ => fun _ => t

def afterRead (t : SirM Empty) (b : ByteArray) : SirM Empty :=
  match t.observe with
  | .impure (.inr (.read _ _)) k => k b
  | _ => t

def afterHalt (t : SirM Empty) (e : Empty) : SirM Empty :=
  match t.observe with
  | .impure (.inl (.halt _)) k => k e
  | _ => t

def initRun (l : Layout noop) (cd : ByteArray) (e : Env) : SirM Empty :=
  skip 1000 (runInner ⟨noop, l, .creation cd, e, .init⟩)

def copied (l : Layout noop) (cd : ByteArray) : ByteArray :=
  (l.init ++ cd).slicePadded (Word.ofU32 l.mainStartOffset.val).toNat (l.main.size : Word).toNat

variable {X : Type} {mem : MemState}

lemma memStep_alloc_zeroed {size : Word} {k : Word → X}
    (h : ∃ a', mem.ValidAlloc size.toNat a') :
    memStep mem (.impure (.inr (.alloc .zeroed size)) k) =
      .branch (.alloc size mem h) fun x =>
        (if size > 0 then mem.push ⟨x.1.start, ⟨.replicate x.1.size 0⟩⟩ else mem, k x.1.start) := by
  show dite _ _ _ = _
  simp only [h, ↓reduceDIte]

lemma memStep_write_empty {w : Word} {bytes : ByteArray} {k : Unit → X} (h : bytes.size = 0) :
    memStep mem (.impure (.inr (.write w bytes)) k) = .silent (mem, k ()) := by
  show ite _ _ _ = _
  simp only [h, ↓reduceIte]

lemma memStep_write {w : Word} {bytes : ByteArray} {k : Unit → X} (h : bytes.size ≠ 0)
    {r : mem.Region w bytes.size} (hr : mem.inBounds w bytes.size = some r) :
    memStep mem (.impure (.inr (.write w bytes)) k) = .silent (mem.write bytes r, k ()) := by
  show ite _ _ _ = _
  simp only [h, hr, ↓reduceIte]

lemma memStep_read_empty {w len : Word} {k : ByteArray → X} (h : len = 0) :
    memStep mem (.impure (.inr (.read w len)) k) = .silent (mem, k .empty) := by
  show ite _ _ _ = _
  simp only [h, ↓reduceIte]

lemma memStep_read {w len : Word} {k : ByteArray → X} (h : len ≠ 0)
    {r : mem.Region w len.toNat} (hr : mem.inBounds w len.toNat = some r) :
    memStep mem (.impure (.inr (.read w len)) k) = .silent (mem, k (mem.read r)) := by
  show ite _ _ _ = _
  simp only [h, hr, ↓reduceIte]

lemma inBounds_singleton (r : NatRange) (a : Allocation) {w : Word} {len : Nat}
    (h : a.start.toNat ≤ w.toNat ∧ w.toNat + len ≤ a.end) :
    MemState.inBounds ⟨r, #[a]⟩ w len = some ⟨⟨0, Nat.zero_lt_one⟩, h⟩ := by
  unfold MemState.inBounds
  show List.findSome? _ [(⟨0, Nat.zero_lt_one⟩ : Fin 1)] = _
  simp [h]

section Steps

variable {op : HostOp} {t : SirM Empty}

lemma Halts.of_eq {m m' : CoFree HostE MemoryND UB} (h : m = m') (hm : Halts op m') : Halts op m :=
  h ▸ hm

lemma Halts.op_eq {op' : HostOp} {m : CoFree HostE MemoryND UB} (h : op = op') (hm : Halts op m) :
    Halts op' m :=
  h ▸ hm

lemma halts_ret {o : SimplifiedOutcome} {k : Empty → SirM Empty}
    (h : t.observe = .impure (.inl (.halt o)) k) : Halts (HostOp.halt o) (CoFree.interp memStep mem t) := by
  obtain ⟨k', _, ho⟩ := observe_interpMem_impure (mem := mem) h
  exact .now ho

lemma halts_alloc {size : Word} {k : Word → SirM Empty}
    (h : t.observe = .impure (.inr (.alloc .zeroed size)) k)
    (hex : ∃ a', mem.ValidAlloc size.toNat a')
    (hk : ∀ x : { a' // mem.ValidAlloc size.toNat a' },
      Halts op (CoFree.interp memStep (if size > 0 then mem.push ⟨x.1.start, ⟨.replicate x.1.size 0⟩⟩ else mem)
        (k x.1.start))) :
    Halts op (CoFree.interp memStep mem t) := by
  obtain ⟨k', hk', ho⟩ := observe_interpMem_impure (mem := mem) h
  exact .branch (ho.trans (congrArg (Step.map _) (memStep_alloc_zeroed hex)))
    fun x => Halts.of_eq (congrArg (CoFree.interp memStep _) (hk' _)) (hk x)

lemma halts_write_empty {w : Word} {bytes : ByteArray} {k : Unit → SirM Empty}
    (h : t.observe = .impure (.inr (.write w bytes)) k) (hb : bytes.size = 0)
    (hk : Halts op (CoFree.interp memStep mem (k ()))) : Halts op (CoFree.interp memStep mem t) := by
  obtain ⟨k', hk', ho⟩ := observe_interpMem_impure (mem := mem) h
  exact .silent (ho.trans (congrArg (Step.map _) (memStep_write_empty hb)))
    (Halts.of_eq (congrArg (CoFree.interp memStep _) (hk' _)) hk)

lemma halts_write {w : Word} {bytes : ByteArray} {k : Unit → SirM Empty}
    (h : t.observe = .impure (.inr (.write w bytes)) k) (hb : bytes.size ≠ 0)
    {r : mem.Region w bytes.size} (hr : mem.inBounds w bytes.size = some r)
    (hk : Halts op (CoFree.interp memStep (mem.write bytes r) (k ()))) : Halts op (CoFree.interp memStep mem t) := by
  obtain ⟨k', hk', ho⟩ := observe_interpMem_impure (mem := mem) h
  exact .silent (ho.trans (congrArg (Step.map _) (memStep_write hb hr)))
    (Halts.of_eq (congrArg (CoFree.interp memStep _) (hk' _)) hk)

lemma halts_read_empty {w len : Word} {k : ByteArray → SirM Empty}
    (h : t.observe = .impure (.inr (.read w len)) k) (hl : len = 0)
    (hk : Halts op (CoFree.interp memStep mem (k .empty))) : Halts op (CoFree.interp memStep mem t) := by
  obtain ⟨k', hk', ho⟩ := observe_interpMem_impure (mem := mem) h
  exact .silent (ho.trans (congrArg (Step.map _) (memStep_read_empty hl)))
    (Halts.of_eq (congrArg (CoFree.interp memStep _) (hk' _)) hk)

lemma halts_read {w len : Word} {k : ByteArray → SirM Empty}
    (h : t.observe = .impure (.inr (.read w len)) k) (hl : len ≠ 0)
    {r : mem.Region w len.toNat} (hr : mem.inBounds w len.toNat = some r)
    (hk : Halts op (CoFree.interp memStep mem (k (mem.read r)))) : Halts op (CoFree.interp memStep mem t) := by
  obtain ⟨k', hk', ho⟩ := observe_interpMem_impure (mem := mem) h
  exact .silent (ho.trans (congrArg (Step.map _) (memStep_read hl hr)))
    (Halts.of_eq (congrArg (CoFree.interp memStep _) (hk' _)) hk)

lemma Halts.of_observe {m m' : CoFree HostE MemoryND UB} (h : m.observe = m'.observe) (hm : Halts op m') :
    Halts op m := by
  cases hm with
  | now h' => exact .now (h.trans h')
  | silent h' hm => exact .silent (h.trans h') hm
  | branch h' hk => exact .branch (h.trans h') hk

lemma observe_interpMem_reserve : ∀ (t : SirM Empty) (hn : 0 < Word.size - CompilerReservedBytes),
    (interpMem t).observe = .branch (MemoryBranchOp.pick (Word.size - CompilerReservedBytes) hn) fun s =>
      CoFree.bind (CoFree.pure (E := HostE) (N := MemoryND) s)
        fun s => CoFree.interp (fun {X} => memStep (X := X))
          { live := #[], reserved := ⟨s.val, CompilerReservedBytes⟩ } t := by
  intro t hn
  kernel_rfl

lemma halts_interpMem :
    (∀ s : Fin (Word.size - CompilerReservedBytes), Halts (E := HostE) op
      (CoFree.interp memStep { live := #[], reserved := ⟨s.val, CompilerReservedBytes⟩ } t)) →
    Halts (E := HostE) op (interpMem t) := by
  intro h
  refine .branch (observe_interpMem_reserve t (by decide)) fun s => Halts.of_observe ?_ (h s)
  rw [observe_bind, observe_pure]
  rfl

end Steps

lemma noop_alloc (l : Layout noop) (cd : ByteArray) (e : Env) :
    (initRun l cd e).observe =
      .impure (.inr (.alloc .zeroed (l.main.size : Word))) (afterAlloc (initRun l cd e)) := by
  kernel_rfl

lemma noop_write (l : Layout noop) (cd : ByteArray) (e : Env) (w : Word) :
    (skip 1000 (afterAlloc (initRun l cd e) w)).observe =
      .impure (.inr (.write w (copied l cd))) (afterWrite (skip 1000 (afterAlloc (initRun l cd e) w))) := by
  kernel_rfl

lemma noop_read (l : Layout noop) (cd : ByteArray) (e : Env) (w : Word) (u : Unit) :
    (skip 1000 (afterWrite (skip 1000 (afterAlloc (initRun l cd e) w)) u)).observe =
      .impure (.inr (.read w (l.main.size : Word)))
        (afterRead (skip 1000 (afterWrite (skip 1000 (afterAlloc (initRun l cd e) w)) u))) := by
  kernel_rfl

lemma noop_ret (l : Layout noop) (cd : ByteArray) (e : Env) (w : Word) (u : Unit) (b : ByteArray) :
    (skip 1000 (afterRead (skip 1000 (afterWrite (skip 1000 (afterAlloc (initRun l cd e) w)) u)) b)).observe =
      .impure (.inl (.halt (.ret b)))
        (afterHalt (skip 1000 (afterRead (skip 1000 (afterWrite (skip 1000 (afterAlloc (initRun l cd e) w)) u)) b))) := by
  kernel_rfl

lemma toNat_mainSize {p : Program} (l : Layout p) : (l.main.size : Word).toNat = l.main.size :=
  Nat.mod_eq_of_lt (Nat.lt_trans l.main_u32 (by decide))

lemma size_copied (l : Layout noop) (cd : ByteArray) : (copied l cd).size = l.main.size := by
  show ((Array.range _).map _).size = _
  rw [Array.size_map, Array.size_range, toNat_mainSize]

lemma copied_eq (l : Layout noop) (cd : ByteArray) : copied l cd = l.main := by
  refine ByteArray.ext_getElem (size_copied l cd) fun i hi hi' => ?_
  have hm := l.mainStartOffset.property i hi'
  have hlt : l.mainStartOffset.val.toNat + i < l.init.size := by
    by_cases h : l.mainStartOffset.val.toNat + i < l.init.size
    · exact h
    · simp [h] at hm
  have hoff : (Word.ofU32 l.mainStartOffset.val).toNat = l.mainStartOffset.val.toNat := by
    show (BitVec.setWidth 256 _).toNat = _
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_trans l.mainStartOffset.val.toBitVec.isLt (by decide))
  have hm' : l.init[l.mainStartOffset.val.toNat + i] = l.main[i] := by
    rw [getElem?_pos l.init _ hlt] at hm
    exact Option.some.inj hm
  have h2 : l.mainStartOffset.val.toNat + i < (l.init ++ cd).size := by
    rw [ByteArray.size_append]; omega
  simp only [copied, ByteArray.slicePadded, ByteArray.getElem_eq_getElem_data, Array.getElem_map, Array.getElem_range,
    hoff, h2, ↓reduceDIte]
  rw [← ByteArray.getElem_eq_getElem_data, ByteArray.getElem_append_left hlt, hm',
    ByteArray.getElem_eq_getElem_data]

lemma inBounds_second (r : NatRange) (a b : Allocation) {w : Word} {len : Nat}
    (ha : ¬(a.start.toNat ≤ w.toNat ∧ w.toNat + len ≤ a.end))
    (hb : b.start.toNat ≤ w.toNat ∧ w.toNat + len ≤ b.end) :
    MemState.inBounds ⟨r, #[a, b]⟩ w len = some ⟨⟨1, Nat.one_lt_two⟩, hb⟩ := by
  unfold MemState.inBounds
  show List.findSome? _ [(⟨0, by decide⟩ : Fin 2), ⟨1, by decide⟩] = _
  simp [ha, hb]

lemma not_within_reserved {res a : Allocation} {len : Nat} (hlen : 0 < len)
    (hd : res.range.Disjoint ⟨a.start.toNat, len⟩) :
    ¬(res.start.toNat ≤ a.start.toNat ∧ a.start.toNat + len ≤ res.end) := by
  simp only [NatRange.Disjoint, NatRange.end, Allocation.range, Allocation.end, Allocation.size] at *
  omega

lemma exists_alloc_after_reserved : ∀ {s : Nat}, s < Word.size - CompilerReservedBytes →
    ∀ {n : Nat}, n < UInt32.size →
    ∃ a', ({ live := #[], reserved := ⟨s, CompilerReservedBytes⟩ } : MemState).ValidAlloc n a' := by
  intro s hs n hn
  have hc : CompilerReservedBytes = 2 ^ 32 := rfl
  generalize CompilerReservedBytes = c at hs hc ⊢
  have hW : Word.size = 2 ^ 256 := rfl
  have hU : UInt32.size = 2 ^ 32 := rfl
  have hrep : (⟨.replicate n 0⟩ : ByteArray).size = n := Array.size_replicate
  have htaken : ({ live := #[], reserved := ⟨s, c⟩ } : MemState).taken = [⟨s, c⟩] := rfl
  rw [hW] at hs
  rw [hU] at hn
  by_cases hfit : s + c + n < 2 ^ 256
  · have hlt : s + c < 2 ^ 256 := by omega
    have hto : (BitVec.ofNat 256 (s + c)).toNat = s + c := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
    refine ⟨⟨BitVec.ofNat 256 (s + c), ⟨.replicate n 0⟩⟩, hrep, ?_, ?_⟩
    · simp only [Allocation.end, Allocation.size, hrep, hto, hW]; omega
    · rw [htaken]
      intro x hx
      obtain rfl := List.mem_singleton.1 hx
      simp only [NatRange.Disjoint, NatRange.end, Allocation.range, Allocation.size, hrep, hto]; omega
  · refine ⟨⟨0, ⟨.replicate n 0⟩⟩, hrep, ?_, ?_⟩
    · simp only [Allocation.end, Allocation.size, hrep, hW]; show 0 + n ≤ _; omega
    · rw [htaken]
      intro x hx
      obtain rfl := List.mem_singleton.1 hx
      simp only [NatRange.Disjoint, NatRange.end, Allocation.range, Allocation.size, hrep]
      show _ ∨ 0 + n ≤ _; omega

lemma noop_init_halts (l : Layout noop) (cd : ByteArray) (e : Env) :
    Halts (HostOp.halt (.ret l.main)) (interpMem (runInner ⟨noop, l, .creation cd, e, .init⟩)) := by
  refine halts_interpMem fun s => ?_
  refine halts_skip 1000 (t := runInner ⟨noop, l, .creation cd, e, .init⟩) ?_
  have hex : ∃ a', ({ live := #[], reserved := ⟨s.val, CompilerReservedBytes⟩ } : MemState).ValidAlloc
      (l.main.size : Word).toNat a' := by
    rw [toNat_mainSize]; exact exists_alloc_after_reserved s.isLt l.main_u32
  refine halts_alloc (noop_alloc l cd e) hex fun ⟨a, ha⟩ => ?_
  refine halts_skip 1000 ?_
  by_cases hn : l.main.size = 0
  · have hw : (l.main.size : Word) = 0 := by rw [hn]; rfl
    have hm : l.main = .empty := ByteArray.ext (Array.eq_empty_of_size_eq_zero hn)
    have hgt : ¬ ((l.main.size : Word) > 0) := by rw [hw]; decide
    simp only [hgt, ↓reduceIte]
    refine halts_write_empty (noop_write l cd e a.start) (by rw [size_copied, hn]) (halts_skip 1000 ?_)
    refine halts_read_empty (noop_read l cd e a.start ()) hw (halts_skip 1000 ?_)
    rw [hm]
    exact halts_ret (noop_ret l cd e a.start () .empty)
  · have hgt : (l.main.size : Word) > 0 := by
      show BitVec.toNat 0 < _
      rw [toNat_mainSize]
      exact Nat.pos_of_ne_zero hn
    simp only [hgt, ↓reduceIte]
    have has : a.size = l.main.size := ha.1.trans (toNat_mainSize l)
    have hsa : (⟨.replicate a.size 0⟩ : ByteArray).size = l.main.size := Array.size_replicate.trans has
    have hss : (a.start - a.start).toNat = 0 := by rw [BitVec.sub_self]; rfl
    let res : NatRange := ⟨s.val, CompilerReservedBytes⟩
    have hw : MemState.inBounds ⟨res, #[⟨a.start, ⟨.replicate a.size 0⟩⟩]⟩ a.start (copied l cd).size =
        some ⟨⟨0, Nat.zero_lt_one⟩, Nat.le_refl _, by
          show a.start.toNat + _ ≤ a.start.toNat + (⟨.replicate a.size 0⟩ : ByteArray).size
          rw [size_copied, hsa]
          exact Nat.le_refl _⟩ :=
      inBounds_singleton _ _ _
    refine halts_write (noop_write l cd e a.start) (by rw [size_copied]; exact hn) hw (halts_skip 1000 ?_)
    have hcs : (copied l cd).copySlice 0 ⟨.replicate a.size 0⟩ (a.start - a.start).toNat
        (copied l cd).size = copied l cd := by
      have hd : (⟨.replicate a.size 0⟩ : ByteArray).data.size = (copied l cd).size := by
        rw [size_copied]; exact hsa
      rw [ByteArray.copySlice_eq_append, hss, ByteArray.extract_same, ByteArray.empty_append,
        Nat.zero_add, ByteArray.extract_zero_size, ByteArray.size_data, Nat.sub_zero, Nat.min_self, Nat.zero_add,
        hd, ByteArray.extract_same, ByteArray.append_empty]
    have hm2 : ∀ h, MemState.write ⟨res, #[⟨a.start, ⟨.replicate a.size 0⟩⟩]⟩ (copied l cd) ⟨⟨0, Nat.zero_lt_one⟩, h⟩ =
        ⟨res, #[⟨a.start, copied l cd⟩]⟩ := fun _ =>
      congrArg (fun b : ByteArray => (⟨res, #[({ start := a.start, bytes := b } : Allocation)]⟩ : MemState)) hcs
    refine Halts.of_eq (congrArg (fun m => CoFree.interp memStep m _) (hm2 _)) ?_
    have hr : MemState.inBounds ⟨res, #[⟨a.start, copied l cd⟩]⟩ a.start (l.main.size : Word).toNat =
        some ⟨⟨0, Nat.zero_lt_one⟩, Nat.le_refl _, by
          show a.start.toNat + _ ≤ a.start.toNat + (copied l cd).size
          rw [size_copied, toNat_mainSize]
          exact Nat.le_refl _⟩ :=
      inBounds_singleton _ _ _
    refine halts_read (noop_read l cd e a.start ()) (fun h => hn (by rw [← toNat_mainSize l, h]; rfl)) hr
      (halts_skip 1000 ?_)
    have hb : ∀ h, MemState.read ⟨res, #[⟨a.start, copied l cd⟩]⟩
        (⟨⟨0, Nat.zero_lt_one⟩, h⟩ : MemState.Region ⟨res, #[⟨a.start, copied l cd⟩]⟩ a.start (l.main.size : Word).toNat) =
        l.main := by
      intro _
      show (copied l cd).extract (a.start - a.start).toNat ((a.start - a.start).toNat + _) = _
      rw [hss, Nat.zero_add, toNat_mainSize, ← size_copied l cd, ByteArray.extract_zero_size, copied_eq]
    exact Halts.op_eq (congrArg (fun b => HostOp.halt (.ret b)) (hb _)) (halts_ret (noop_ret l cd e a.start () _))

lemma noop_stop (l : Layout noop) (st : Bool) (cd : BytesX32) (e : Env) (imm : Immutables noop .call) :
    (skip 1000 (runInner ⟨noop, l, .call st cd, e, imm⟩)).observe =
      .impure (.inl (.halt (.ret .empty))) (afterHalt (skip 1000 (runInner ⟨noop, l, .call st cd, e, imm⟩))) := by
  kernel_rfl

lemma noop_main_returns (l : Layout noop) (imms : MainImmutables) (st : Bool) (cd : BytesX32) (e : Env)
    (w₀ : World) : Returns (.inr (.ret .empty w₀.store)) (noop.runMain l imms st cd e w₀) :=
  Halts.interpHost ⟨w₀, .empty⟩ (halts_interpMem fun _ => halts_skip 1000 (halts_ret (noop_stop l st cd e _)))

lemma noop_mainSafe (l : Layout noop) (imms : MainImmutables) : MainSafe noop l imms :=
  fun e st cd w₀ => (noop_main_returns l imms st cd e w₀).deterministic

def noopLayout : Layout noop where
  init := ⟨#[0]⟩
  init_u32 := by decide
  main := ⟨#[0]⟩
  main_u32 := by decide
  mainStartOffset := ⟨0, fun | 0, _ => rfl⟩
  initDataOffsets := nofun
  mainDataOffsets := nofun
  immutableOffsets := nofun
  atLeastOne_immOffsets := nofun
  no_imm_imm_overlap := nofun
  no_imm_data_overlap := nofun

def stopsLayout : Layout initStops where
  init := ⟨#[0]⟩
  init_u32 := by decide
  main := ⟨#[0]⟩
  main_u32 := by decide
  mainStartOffset := ⟨0, fun | 0, _ => rfl⟩
  initDataOffsets := nofun
  mainDataOffsets := nofun
  immutableOffsets := nofun
  atLeastOne_immOffsets := nofun
  no_imm_imm_overlap := nofun
  no_imm_data_overlap := nofun

def stopsEnv : Env where
  address := 0
  origin := 0
  caller := 0
  callvalue := 0
  gasprice := 0
  chainid := 0
  coinbase := 0
  timestamp := 0
  number := 0
  prevrandao := 0
  gaslimit := 0
  basefee := 0
  blobbasefee := 0
  blockhash _ := 0
  blobhash _ := 0

lemma initStops_stop :
    (skip 1000 (runInner ⟨initStops, stopsLayout, .creation .empty, stopsEnv, .init⟩)).observe =
      .impure (.inl (.halt (.ret .empty))) (afterHalt (skip 1000 (runInner ⟨initStops, stopsLayout, .creation .empty, stopsEnv, .init⟩))) := by
  kernel_rfl

def stopsState : World := ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun _ => 0, fun _ => .empty⟩⟩

lemma stopsState_unset : stopsState.Unset stopsEnv.address :=
  ⟨fun _ => rfl, fun _ => rfl, rfl⟩


lemma stopsLayout_withSetImmutables_ne (imms : MainImmutables) :
    stopsLayout.withSetImmutables imms ≠ some .empty := by
  unfold Layout.withSetImmutables
  split
  next hwf =>
    intro heq
    have := congrArg ByteArray.size (Option.some.inj heq)
    have hset : stopsLayout.setImmutables ⟨imms.slots, hwf.1⟩ = ⟨#[0]⟩ := rfl
    rw [ByteArray.size_append, hset] at this
    rw [show (⟨#[0]⟩ : ByteArray).size = 1 from rfl, show ByteArray.empty.size = 0 from rfl] at this
    omega
  next => nofun

lemma Returns.runInit {p : Program} {l : Layout p} {cd : ByteArray} {env : Env} {w₀ : World}
    {main : ByteArray} {s' : Store} (h : Returns (.inr (.ret main s')) (p.run l (.creation cd) env .init w₀)) :
    Returns (match l.toMainImmutables main with
      | some m => .inr (.ret m s')
      | none => .inl .unsoundMain) (p.runInit l cd env w₀) := by
  exact h.map _ rfl

lemma noop_init_returns (l : Layout noop) (cd : ByteArray) (e : Env) (w₀ : World) :
    Returns (.inr (.ret ⟨#[], .empty⟩ w₀.store)) (noop.runInit l cd e w₀) := by
  have h := ((noop_init_halts l cd e).interpHost (self := e.address) ⟨w₀, .empty⟩).runInit
  have hm : l.toMainImmutables l.main = some ⟨#[], .empty⟩ :=
    (Layout.toMainImmutables_eq_some_iff _ _ _).2
      (by
        simp only [Layout.withSetImmutables, show (⟨#[], .empty⟩ : MainImmutables).WF noop by decide, ↓reduceDIte]
        exact congrArg some (congrArg (· ++ ByteArray.empty) (rfl : l.setImmutables #v[] = l.main) |>.trans
          ByteArray.append_empty))
  rw [hm] at h
  exact h

lemma initStops_returns :
    Returns (.inl .unsoundMain)
      (initStops.runInit stopsLayout .empty stopsEnv stopsState) := by
  have h := (Halts.interpHost ⟨stopsState, .empty⟩
    (halts_interpMem fun _ => halts_skip 1000 (halts_ret initStops_stop))).runInit
  rcases hm : stopsLayout.toMainImmutables .empty with _ | m
  · rw [hm] at h; exact h
  · exact absurd ((Layout.toMainImmutables_eq_some_iff _ _ _).1 hm) (stopsLayout_withSetImmutables_ne m)

end SirTests.Safety
