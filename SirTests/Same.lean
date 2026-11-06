import SirTests.Host
import SirTests.KernelRfl
import ITree.Same.Theorems
import Sir.Syntax
import SirTests.Safety.Proofs

/-! `Same` on small programs, run with memory interpreted. The runs are
computed by the kernel (`kernel_rfl`) up to their next host operation; after an allocation the placement stays a variable, so the rest of the run is
computed for every placement at once. -/

namespace SirTests.Same

open Sir Host CoFree

/-! ## Stepping through a run -/

/-- Follows at most `n` `silent` nodes. -/
def skip {A : Type} : Nat → CoFree HostE MemoryND A → CoFree HostE MemoryND A
  | 0, t => t
  | n + 1, t => match t.observe with
    | .silent t' => skip n t'
    | _ => t

def headOp {A : Type} (t : CoFree HostE MemoryND A) : Option HostOp :=
  match t.observe with
  | .impure op _ => some op
  | _ => none

open Classical in
/-- `t` after answering `r`, if `t` performs `op` next. -/
noncomputable def resume {A : Type} (t : CoFree HostE MemoryND A) (op : HostOp) (r : HostOp.Resp op) :
    CoFree HostE MemoryND A :=
  match t.observe with
  | .impure op' k => if h : op' = op then k (h ▸ r) else t
  | _ => t

def headBr {A : Type} (t : CoFree HostE MemoryND A) : Option MemoryBranchOp :=
  match t.observe with
  | .branch c _ => some c
  | _ => none

lemma observe_of_headOp {A : Type} {t : CoFree HostE MemoryND A} {op : HostOp} (h : headOp t = some op) :
    t.observe = .impure op (resume t op) := by
  unfold headOp at h
  split at h
  next op' k hk =>
    cases h
    unfold resume
    simp only [hk, dite_true]
  next => cases h

variable {A B : Type} {RR : A → B → Prop}

lemma same_skipL (n : Nat) {N : NonDeterminism} {t₁ : CoFree HostE MemoryND A} {t₂ : CoFree HostE N B}
    (h : Same RR (skip n t₁) t₂) : Same RR t₁ t₂ := by
  induction n generalizing t₁ with
  | zero => exact h
  | succ n ih =>
    unfold skip at h
    split at h
    next t' ht => exact Same.silentL ht (ih h)
    next => exact h

lemma same_skipR (n : Nat) {N : NonDeterminism} {t₁ : CoFree HostE N A} {t₂ : CoFree HostE MemoryND B}
    (h : Same RR t₁ (skip n t₂)) : Same RR t₁ t₂ := by
  induction n generalizing t₂ with
  | zero => exact h
  | succ n ih =>
    unfold skip at h
    split at h
    next t' ht => exact Same.silentR ht (ih h)
    next => exact h

lemma skipL_inv (n : Nat) {N : NonDeterminism} {t₁ : CoFree HostE MemoryND A} {t₂ : CoFree HostE N B}
    (h : Same RR t₁ t₂) : Same RR (skip n t₁) t₂ := by
  induction n generalizing t₁ with
  | zero => exact h
  | succ n ih =>
    unfold skip
    split
    next t' ht => exact ih (Same.silentL_inv h ht)
    next => exact h

lemma skipR_inv (n : Nat) {N : NonDeterminism} {t₁ : CoFree HostE N A} {t₂ : CoFree HostE MemoryND B}
    (h : Same RR t₁ t₂) : Same RR t₁ (skip n t₂) := by
  induction n generalizing t₂ with
  | zero => exact h
  | succ n ih =>
    unfold skip
    split
    next t' ht => exact ih (Same.silentR_inv h ht)
    next => exact h

lemma not_same_pure_impure {N₁ N₂ : NonDeterminism} {m₁ : CoFree HostE N₁ A} {m₂ : CoFree HostE N₂ B}
    {a : A} {op : HostOp} {k : HostOp.Resp op → CoFree HostE N₂ B} (h₁ : m₁.observe = .pure a)
    (h₂ : m₂.observe = .impure op k) : ¬Same RR m₁ m₂ := by
  intro h
  cases h.unfold with
  | ret _ _ _ h₂' => rw [h₂] at h₂'; cases h₂'
  | impure _ h₁' => rw [h₁] at h₁'; cases h₁'
  | silentL h₁' => rw [h₁] at h₁'; cases h₁'
  | silentR h₂' => rw [h₂] at h₂'; cases h₂'
  | branchL _ h₁' => rw [h₁] at h₁'; cases h₁'
  | branchR _ h₂' => rw [h₂] at h₂'; cases h₂'
  | mutualUnobservedStep hu => unfold ForallUnobserved at hu; rw [h₁] at hu; exact hu

/-! ## Programs -/

def run (p : Program) (l : Layout p := by exact plainLayout _) : CoFree HostE MemoryND UB :=
  interpMem (runInner ⟨p, l, .creation .empty, testEnv, .init⟩)

abbrev Reserved := Fin (Word.size - CompilerReservedBytes)

def memAt (s : Reserved) : MemState := { live := #[], reserved := ⟨s.val, CompilerReservedBytes⟩ }

def initOf (p : Program) (l : Layout p := by exact plainLayout _) : SirM Empty :=
  runInner ⟨p, l, .creation .empty, testEnv, .init⟩

def runAt (p : Program) (s : Reserved) (l : Layout p := by exact plainLayout _) : CoFree HostE MemoryND UB :=
  CoFree.interp memStep (memAt s) (initOf p l)

def allocCont (p : Program) (l : Layout p := by exact plainLayout _) : Word → SirM Empty :=
  Safety.afterAlloc (Safety.skip 100 (initOf p l))

lemma observe_run : ∀ (p : Program) (l : Layout p),
    (run p l).observe = .branch (MemoryBranchOp.pick _ (by decide)) fun s =>
      CoFree.bind (CoFree.pure (E := HostE) (N := MemoryND) s)
        fun s => CoFree.interp (fun {X} => memStep (X := X)) (memAt s)
          (runInner ⟨p, l, .creation .empty, testEnv, .init⟩) := by
  intro p l
  exact Safety.observe_interpMem_reserve _ _

lemma observe_run_cont : ∀ (p : Program) (l : Layout p) (s : Reserved),
    (CoFree.bind (CoFree.pure (E := HostE) (N := MemoryND) s)
      fun s => CoFree.interp (fun {X} => memStep (X := X)) (memAt s)
        (runInner ⟨p, l, .creation .empty, testEnv, .init⟩)).observe = (runAt p s l).observe := by
  intro p l s
  rw [observe_bind, observe_pure]
  rfl

def memAfter (kind : AllocKind) (size : Word) (mem : MemState) (a' : Allocation) : MemState :=
  let a' := match kind with
    | .zeroed => { a' with bytes := ⟨.replicate a'.size 0⟩ }
    | .uninitialized => a'
  if size > 0 then mem.push a' else mem

lemma observe_interp_alloc : ∀ {mem : MemState} {t : SirM Empty} {kind : AllocKind} {size : Word}
    {k : Word → SirM Empty}, t.observe = .impure (.inr (.alloc kind size)) k →
    ∀ hex : ∃ a', mem.ValidAlloc size.toNat a',
    (CoFree.interp memStep mem t).observe = .branch (.alloc size mem hex) fun x =>
      CoFree.interp memStep (memAfter kind size mem x.1) (k x.1.start) := by
  intro mem t kind size k h hex
  obtain ⟨k', hk', ho⟩ := Safety.observe_interpMem_impure (mem := mem) h
  rw [ho]
  show Step.map _ (dite _ _ _) = _
  simp only [hex, ↓reduceDIte, Step.map]
  congr
  funext ⟨a', _⟩
  cases kind <;> exact congrArg (CoFree.interp memStep _) (hk' _)

section Run

variable {B : Type} {R : UB → B → Prop} {N : NonDeterminism}

lemma same_run : ∀ {p₁ p₂ : Program} {l₁ : Layout p₁} {l₂ : Layout p₂} {R : UB → UB → Prop},
    (∀ s₁ s₂, Same R (runAt p₁ s₁ l₁) (runAt p₂ s₂ l₂)) → Same R (run p₁ l₁) (run p₂ l₂) := by
  intro p₁ p₂ l₁ l₂ R h
  exact Same.branch (observe_run p₁ l₁) (observe_run p₂ l₂) fun s₁ s₂ =>
    Same.congr (h s₁ s₂) (observe_run_cont p₁ l₁ s₁).symm (observe_run_cont p₂ l₂ s₂).symm

lemma same_runL : ∀ {p : Program} {l : Layout p} {t₂ : CoFree HostE N B},
    (∀ s, Same R (runAt p s l) t₂) → Same R (run p l) t₂ := by
  intro p l t₂ h
  exact Same.branchL _ (observe_run p l) fun s => Same.congr (h s) (observe_run_cont p l s).symm rfl

lemma run_invL : ∀ {p : Program} {l : Layout p} {t₂ : CoFree HostE N B},
    Same R (run p l) t₂ → ∀ s, Same R (runAt p s l) t₂ := by
  intro p l t₂ h s
  exact Same.congr (Same.branchL_inv h (observe_run p l) s) (observe_run_cont p l s) rfl

lemma run_invR : ∀ {A : Type} {R : A → UB → Prop} {t₁ : CoFree HostE N A} {p : Program} {l : Layout p},
    Same R t₁ (run p l) → ∀ s, Same R t₁ (runAt p s l) := by
  intro A R t₁ p l h s
  exact Same.congr (Same.branchR_inv h (observe_run p l) s) rfl (observe_run_cont p l s)

lemma same_skipSL : ∀ (n : Nat) {mem : MemState} {t : SirM Empty} {t₂ : CoFree HostE N B},
    Same R (CoFree.interp memStep mem (Safety.skip n t)) t₂ → Same R (CoFree.interp memStep mem t) t₂ := by
  intro n
  induction n with
  | zero => intro _ _ _ h; exact h
  | succ n ih =>
    intro mem t t₂ h
    unfold Safety.skip at h
    split at h
    next t' ht => exact Same.silentL (Safety.observe_interpMem_silent ht) (ih h)
    next => exact h

lemma same_skipSR : ∀ (n : Nat) {A : Type} {R : A → UB → Prop} {mem : MemState} {t₁ : CoFree HostE N A}
    {t : SirM Empty},
    Same R t₁ (CoFree.interp memStep mem (Safety.skip n t)) → Same R t₁ (CoFree.interp memStep mem t) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; exact h
  | succ n ih =>
    intro A R mem t₁ t h
    unfold Safety.skip at h
    split at h
    next t' ht => exact Same.silentR (Safety.observe_interpMem_silent ht) (ih h)
    next => exact h

lemma skipSL_inv : ∀ (n : Nat) {mem : MemState} {t : SirM Empty} {t₂ : CoFree HostE N B},
    Same R (CoFree.interp memStep mem t) t₂ → Same R (CoFree.interp memStep mem (Safety.skip n t)) t₂ := by
  intro n
  induction n with
  | zero => intro _ _ _ h; exact h
  | succ n ih =>
    intro mem t t₂ h
    unfold Safety.skip
    split
    next t' ht => exact ih (Same.silentL_inv h (Safety.observe_interpMem_silent ht))
    next => exact h

lemma skipSR_inv : ∀ (n : Nat) {A : Type} {R : A → UB → Prop} {mem : MemState} {t₁ : CoFree HostE N A}
    {t : SirM Empty},
    Same R t₁ (CoFree.interp memStep mem t) → Same R t₁ (CoFree.interp memStep mem (Safety.skip n t)) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; exact h
  | succ n ih =>
    intro A R mem t₁ t h
    unfold Safety.skip
    split
    next t' ht => exact ih (Same.silentR_inv h (Safety.observe_interpMem_silent ht))
    next => exact h

end Run

lemma exists_alloc_memAt : ∀ (s : Reserved) (n : Word), n.toNat < UInt32.size →
    ∃ a', (memAt s).ValidAlloc n.toNat a' := by
  intro s n hn
  exact Safety.exists_alloc_after_reserved s.isLt hn

/-- `stop`, which is `ret` with no data. -/
abbrev stopOp : HostOp := .halt (.ret .empty)

def afterStore {A : Type} (t : CoFree HostE MemoryND A) : Unit → CoFree HostE MemoryND A :=
  match t.observe with
  | .impure (.sstore _ _) k => k
  | _ => fun _ => t

lemma sstore_ne {k v w : Word} (h : v ≠ w) : HostOp.sstore k v ≠ HostOp.sstore k w :=
  fun e => h (HostOp.sstore.inj e).2

def stops : Program := sir! {
  fn init:
    entry { stop }
  fn main:
    entry { stop }
}

/-- Allocates, computes with the pointer, and never observes it. -/
def mallocs : Program := sir! {
  fn init:
    entry {
      p = malloc 32
      q = add p p
      stop
    }
  fn main:
    entry { stop }
}

def mallocsAny : Program := sir! {
  fn init:
    entry {
      p = mallocany 64
      stop
    }
  fn main:
    entry { stop }
}

def stores (v : Word) : Program := sir! {
  fn init:
    entry {
      sstore 0 (v)
      stop
    }
  fn main:
    entry { stop }
}

/-- `stores 1` after a jump, which is one more silent step. -/
def jumpsThenStores : Program := sir! {
  fn init:
    entry { => @store }
    store {
      sstore 0 1
      stop
    }
  fn main:
    entry { stop }
}

/-- `stores 1` after reading the environment, which is not a host operation. -/
def readsEnvThenStores : Program := sir! {
  fn init:
    entry {
      k = const 0
      v = const 1
      c = caller
      d = calldataload k
      b = blockhash k
      sstore k v
      stop
    }
  fn main:
    entry { stop }
}

/-- `sstore 0 5`, then `sstore 1 (sload 0)`. -/
def storeLoads : Program := sir! {
  fn init:
    entry {
      k = const 0
      sstore k 5
      x = sload k
      sstore 1 x
      stop
    }
  fn main:
    entry { stop }
}

/-- Stores the pointer it allocated. -/
def leaks : Program := sir! {
  fn init:
    entry {
      p = malloc 32
      sstore 0 p
      stop
    }
  fn main:
    entry { stop }
}

/-- UB `switchNoMatch`. -/
def switchUB : Program := sir! {
  fn init:
    entry {
      x = const 5
      switch x { 0 => @entry }
    }
  fn main:
    entry { stop }
}

/-- Malformed: `sstore`s an undefined variable. -/
def undefinedVar : Program := sir! {
  fn init:
    entry {
      sstore $1 $1
      stop
    }
  fn main:
    entry { stop }
}

/-- Halts exceptionally, as invalid EVM code does. -/
def halts : Program := sir! {
  fn init:
    entry { invalid }
  fn main:
    entry { stop }
}

/-- UB `memoryOutOfBounds`: reads memory that was never allocated. -/
def readUB : Program := sir! {
  fn init:
    entry {
      x = mload256 0
      stop
    }
  fn main:
    entry { stop }
}

/-! ## Equivalent -/

/-- Placements are answered independently on each side, and the pointer is never observed. -/
theorem mallocs_same_mallocsAny : Same Eq (run mallocs) (run mallocsAny) := by
  refine same_run fun s₁ s₂ => ?_
  apply same_skipSL 100; apply same_skipSR 100
  have h₁ := observe_interp_alloc (mem := memAt s₁) (t := Safety.skip 100 (initOf mallocs)) (kind := .zeroed)
    (size := 32) (k := allocCont mallocs) (by kernel_rfl) (exists_alloc_memAt s₁ 32 (by decide))
  have h₂ := observe_interp_alloc (mem := memAt s₂) (t := Safety.skip 100 (initOf mallocsAny))
    (kind := .uninitialized) (size := 64) (k := allocCont mallocsAny) (by kernel_rfl)
    (exists_alloc_memAt s₂ 64 (by decide))
  refine Same.branch h₁ h₂ fun r₁ r₂ => ?_
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

/-- An allocation on one side only is skipped like any silent step. -/
theorem mallocs_same_stops : Same Eq (run mallocs) (run stops) := by
  refine same_run fun s₁ s₂ => ?_
  apply same_skipSL 100; apply same_skipR 100
  have h₁ := observe_interp_alloc (mem := memAt s₁) (t := Safety.skip 100 (initOf mallocs)) (kind := .zeroed)
    (size := 32) (k := allocCont mallocs) (by kernel_rfl) (exists_alloc_memAt s₁ 32 (by decide))
  refine Same.branchL _ h₁ fun r => ?_
  apply same_skipL 100
  exact Same.impure (op := stopOp) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

theorem mallocs_deterministic : Deterministic (run mallocs) :=
  (Deterministic.of_same mallocs_same_stops).1

/-- What a compiler may emit for `mallocs`: it stops, with no allocation and so no choice. -/
def stopsTarget : CoFree HostE .none UB := (CoFree.perform stopOp).bind nofun

/-- A run with nondeterminism relates to one without: only operations are compared. -/
theorem mallocs_same_stopsTarget : Same Eq (run mallocs) stopsTarget := by
  refine same_runL fun s => ?_
  apply same_skipSL 100
  have h₁ := observe_interp_alloc (mem := memAt s) (t := Safety.skip 100 (initOf mallocs)) (kind := .zeroed)
    (size := 32) (k := allocCont mallocs) (by kernel_rfl) (exists_alloc_memAt s 32 (by decide))
  refine Same.branchL _ h₁ fun r => ?_
  apply same_skipL 100
  refine Same.impure stopOp (k₂ := fun r => (CoFree.pure r).bind nofun)
    (observe_of_headOp (by kernel_rfl)) ?_ fun r => Empty.elim r
  kernel_rfl

theorem stores_same_jumpsThenStores : Same Eq (run (stores 1)) (run jumpsThenStores) := by
  refine same_run fun s₁ s₂ => ?_
  apply same_skipL 100; apply same_skipR 100
  refine Same.impure (.sstore 0 1) (k₁ := afterStore (skip 100 (runAt (stores 1) s₁)))
    (k₂ := afterStore (skip 100 (runAt jumpsThenStores s₂))) ?_ ?_ fun r => ?_
  · kernel_rfl
  · kernel_rfl
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

theorem stores_same_readsEnvThenStores : Same Eq (run (stores 1)) (run readsEnvThenStores) := by
  refine same_run fun s₁ s₂ => ?_
  apply same_skipL 100; apply same_skipR 100
  refine Same.impure (.sstore 0 1) (k₁ := afterStore (skip 100 (runAt (stores 1) s₁)))
    (k₂ := afterStore (skip 100 (runAt readsEnvThenStores s₂))) ?_ ?_ fun r => ?_
  · kernel_rfl
  · kernel_rfl
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

/-- Undefined behavior relates to the same undefined behavior. -/
theorem switchUB_same_switchUB : Same Eq (run switchUB) (run switchUB) := by
  refine same_run fun s₁ s₂ => ?_
  apply same_skipL 100; apply same_skipR 100
  exact Same.ret (a := .switchNoMatch) (b := .switchNoMatch) (by kernel_rfl) (by kernel_rfl) rfl

/-! ## Not equivalent -/

def reserved₀ : Reserved := ⟨0, by decide⟩

theorem stores_not_same : ¬Same Eq (run (stores 1)) (run (stores 2)) := by
  intro h
  have h := run_invR (run_invL h reserved₀) reserved₀
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact sstore_ne (by decide) (Same.impure_inv h (observe_of_headOp (op := .sstore 0 1)
    (by kernel_rfl)) (observe_of_headOp (op := .sstore 0 2) (by kernel_rfl)))

theorem switchUB_not_same_stops : ¬Same Eq (run switchUB) (run stops) := by
  intro h
  have h := run_invR (run_invL h reserved₀) reserved₀
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact not_same_pure_impure (a := .switchNoMatch) (by kernel_rfl)
    (observe_of_headOp (op := stopOp) (by kernel_rfl)) h

/-- Undefined behavior of different kinds is not related: their payloads differ. -/
theorem switchUB_not_same_readUB : ¬Same Eq (run switchUB) (run readUB) := by
  intro h
  have h := run_invR (run_invL h reserved₀) reserved₀
  have h := skipR_inv 100 (skipL_inv 100 h)
  have := Same.ret_inv h (a := .switchNoMatch) (b := .memoryOutOfBounds 0 32) (by kernel_rfl)
    (by kernel_rfl)
  nomatch this

/-- A malformed program is UB, not related to a valid exceptional halt. -/
theorem undefinedVar_not_same_halts : ¬Same Eq (run undefinedVar) (run halts) := by
  intro h
  have h := run_invR (run_invL h reserved₀) reserved₀
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact not_same_pure_impure (a := .malformed "undefined var") (by kernel_rfl)
    (observe_of_headOp (op := .halt .invalid) (by kernel_rfl)) h

/-- `Same` is not reflexive: a run that stores a pointer depends on where it was placed. -/
theorem leaks_not_deterministic : ¬Deterministic (run leaks) := by
  intro h
  have h := run_invR (run_invL h reserved₀) reserved₀
  have h := skipSR_inv 100 (skipSL_inv 100 h)
  have hex := exists_alloc_memAt reserved₀ 32 (by decide)
  have hal := observe_interp_alloc (mem := memAt reserved₀) (t := Safety.skip 100 (initOf leaks))
    (kind := .zeroed) (size := 32) (k := allocCont leaks) (by kernel_rfl) hex
  have h := Same.branchL_inv h hal ⟨⟨(2 ^ 32 : Nat), ⟨.replicate 32 0⟩⟩, by decide⟩
  have h := Same.branchR_inv h hal ⟨⟨(2 ^ 32 + 32 : Nat), ⟨.replicate 32 0⟩⟩, by decide⟩
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact sstore_ne (by decide) (Same.impure_inv h (observe_of_headOp (op := .sstore 0 (2 ^ 32 : Nat))
    (by kernel_rfl)) (observe_of_headOp (op := .sstore 0 (2 ^ 32 + 32 : Nat)) (by kernel_rfl)))

end SirTests.Same
