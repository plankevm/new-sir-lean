import SirTests.Host
import SirTests.KernelRfl
import ITree.Same.Theorems
import Sir.Syntax

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

def allocOp (n : Word) (h : ∃ a', ValidAlloc [] n.toNat a') : MemoryBranchOp := .alloc n [] h

/-- `t` after placing a first allocation of `n` bytes with `r`, if `t` makes it next. -/
def resumeBr {A : Type} (t : CoFree HostE MemoryND A) (n : Word)
    (r : { a' // ValidAlloc [] n.toNat a' }) : CoFree HostE MemoryND A :=
  match t.observe with
  | .branch (.alloc n' [] _) k => if h : n' = n then k (h ▸ r) else t
  | _ => t

lemma observe_of_headBr {A : Type} {t : CoFree HostE MemoryND A} (n : Word)
    (hex : ∃ a', ValidAlloc [] n.toNat a' := by decide) (h : headBr t = some (allocOp n hex)) :
    t.observe = .branch (allocOp n hex) (resumeBr t n) := by
  unfold headBr at h
  split at h
  next c' k hk =>
    cases h
    unfold resumeBr
    simp only [hk, allocOp, dite_true]
  next => cases h

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
  apply same_skipL 100; apply same_skipR 100
  refine Same.branch (observe_of_headBr 32 (h := by kernel_rfl))
    (observe_of_headBr 64 (h := by kernel_rfl)) fun r₁ r₂ => ?_
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

/-- An allocation on one side only is skipped like any silent step. -/
theorem mallocs_same_stops : Same Eq (run mallocs) (run stops) := by
  apply same_skipL 100; apply same_skipR 100
  refine Same.branchL _ (observe_of_headBr 32 (h := by kernel_rfl))
    fun r => ?_
  apply same_skipL 100
  exact Same.impure (op := stopOp) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

theorem mallocs_deterministic : Deterministic (run mallocs) :=
  (Deterministic.of_same mallocs_same_stops).1

/-- What a compiler may emit for `mallocs`: it stops, with no allocation and so no choice. -/
def stopsTarget : CoFree HostE .none UB := (CoFree.perform stopOp).bind nofun

/-- A run with nondeterminism relates to one without: only operations are compared. -/
theorem mallocs_same_stopsTarget : Same Eq (run mallocs) stopsTarget := by
  apply same_skipL 100
  refine Same.branchL _ (observe_of_headBr 32 (h := by kernel_rfl))
    fun r => ?_
  apply same_skipL 100
  refine Same.impure stopOp (k₂ := fun r => (CoFree.pure r).bind nofun)
    (observe_of_headOp (by kernel_rfl)) ?_ fun r => Empty.elim r
  kernel_rfl

theorem stores_same_jumpsThenStores : Same Eq (run (stores 1)) (run jumpsThenStores) := by
  apply same_skipL 100; apply same_skipR 100
  refine Same.impure (.sstore 0 1) (k₁ := afterStore (skip 100 (run (stores 1))))
    (k₂ := afterStore (skip 100 (run jumpsThenStores))) ?_ ?_ fun r => ?_
  · kernel_rfl
  · kernel_rfl
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

theorem stores_same_readsEnvThenStores : Same Eq (run (stores 1)) (run readsEnvThenStores) := by
  apply same_skipL 100; apply same_skipR 100
  refine Same.impure (.sstore 0 1) (k₁ := afterStore (skip 100 (run (stores 1))))
    (k₂ := afterStore (skip 100 (run readsEnvThenStores))) ?_ ?_ fun r => ?_
  · kernel_rfl
  · kernel_rfl
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

/-- Undefined behavior relates to the same undefined behavior. -/
theorem switchUB_same_switchUB : Same Eq (run switchUB) (run switchUB) := by
  apply same_skipL 100; apply same_skipR 100
  exact Same.ret (a := .switchNoMatch) (b := .switchNoMatch) (by kernel_rfl) (by kernel_rfl) rfl

/-! ## Not equivalent -/

theorem stores_not_same : ¬Same Eq (run (stores 1)) (run (stores 2)) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact sstore_ne (by decide) (Same.impure_inv h (observe_of_headOp (op := .sstore 0 1)
    (by kernel_rfl)) (observe_of_headOp (op := .sstore 0 2) (by kernel_rfl)))

theorem switchUB_not_same_stops : ¬Same Eq (run switchUB) (run stops) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact not_same_pure_impure (a := .switchNoMatch) (by kernel_rfl)
    (observe_of_headOp (op := stopOp) (by kernel_rfl)) h

/-- Undefined behavior of different kinds is not related: their payloads differ. -/
theorem switchUB_not_same_readUB : ¬Same Eq (run switchUB) (run readUB) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  have := Same.ret_inv h (a := .switchNoMatch) (b := .memoryOutOfBounds 0 32) (by kernel_rfl)
    (by kernel_rfl)
  nomatch this

/-- A malformed program is UB, not related to a valid exceptional halt. -/
theorem undefinedVar_not_same_halts : ¬Same Eq (run undefinedVar) (run halts) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact not_same_pure_impure (a := .malformed "undefined var") (by kernel_rfl)
    (observe_of_headOp (op := .halt .invalid) (by kernel_rfl)) h

/-- `Same` is not reflexive: a run that stores a pointer depends on where it was placed. -/
theorem leaks_not_deterministic : ¬Deterministic (run leaks) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  have h := Same.branchL_inv h (observe_of_headBr 32 (h := by kernel_rfl)) ⟨⟨0, ⟨.replicate 32 0⟩⟩, by decide⟩
  have h := Same.branchR_inv h (observe_of_headBr 32 (h := by kernel_rfl))
    ⟨⟨32, ⟨.replicate 32 0⟩⟩, by decide⟩
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact sstore_ne (by decide) (Same.impure_inv h (observe_of_headOp (op := .sstore 0 0)
    (by kernel_rfl)) (observe_of_headOp (op := .sstore 0 32) (by kernel_rfl)))

end SirTests.Same
