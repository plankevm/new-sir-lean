import SirTests.Host
import SirTests.KernelRfl

/-! `Same` on small programs, run with concrete storage from the default state. The runs are
computed by the kernel (`kernel_rfl`) up to their next world operation; after an allocation the placement stays a variable, so the rest of the run is
computed for every placement at once. -/

namespace SirTests.Same

open Sir Host CoFree

/-! ## Stepping through a run -/

/-- Follows at most `n` `silent` nodes. -/
def skip {A : Type} : Nat → CoFree Exec SirND A → CoFree Exec SirND A
  | 0, t => t
  | n + 1, t => match t.observe with
    | .silent t' => skip n t'
    | _ => t

def headOp {A : Type} (t : CoFree Exec SirND A) : Option (WorldOp) :=
  match t.observe with
  | .impure op _ => some op
  | _ => none

open Classical in
/-- `t` after answering `r`, if `t` performs `op` next. -/
noncomputable def resume {A : Type} (t : CoFree Exec SirND A) (op : WorldOp) (r : WorldOp.Resp op) :
    CoFree Exec SirND A :=
  match t.observe with
  | .impure op' k => if h : op' = op then k (h ▸ r) else t
  | _ => t

def headBr {A : Type} (t : CoFree Exec SirND A) : Option Choice :=
  match t.observe with
  | .branch c _ => some c
  | _ => none

/-- `t` after placing with `r`, if `t` branches on `c` next. -/
def resumeBr {A : Type} (t : CoFree Exec SirND A) (c : Choice) (r : Choice.Resp c) : CoFree Exec SirND A :=
  match t.observe with
  | .branch c' k => if h : c' = c then k (h ▸ r) else t
  | _ => t

theorem observe_of_headBr {A : Type} {t : CoFree Exec SirND A} {c : Choice} (h : headBr t = some c) :
    t.observe = .branch c (resumeBr t c) := by
  unfold headBr at h
  split at h
  next c' k hk =>
    cases h
    unfold resumeBr
    simp only [hk, dite_true]
  next => cases h

theorem observe_of_headOp {A : Type} {t : CoFree Exec SirND A} {op : WorldOp} (h : headOp t = some op) :
    t.observe = .impure op (resume t op) := by
  unfold headOp at h
  split at h
  next op' k hk =>
    cases h
    unfold resume
    simp only [hk, dite_true]
  next => cases h

variable {A B : Type} {RR : A → B → Prop}

theorem same_skipL (n : Nat) {N : NonDeterminism} {t₁ : CoFree Exec SirND A} {t₂ : CoFree Exec N B}
    (h : Same RR (skip n t₁) t₂) : Same RR t₁ t₂ := by
  induction n generalizing t₁ with
  | zero => exact h
  | succ n ih =>
    unfold skip at h
    split at h
    next t' ht => exact Same.silentL ht (ih h)
    next => exact h

theorem same_skipR (n : Nat) {N : NonDeterminism} {t₁ : CoFree Exec N A} {t₂ : CoFree Exec SirND B}
    (h : Same RR t₁ (skip n t₂)) : Same RR t₁ t₂ := by
  induction n generalizing t₂ with
  | zero => exact h
  | succ n ih =>
    unfold skip at h
    split at h
    next t' ht => exact Same.silentR ht (ih h)
    next => exact h

theorem skipL_inv (n : Nat) {N : NonDeterminism} {t₁ : CoFree Exec SirND A} {t₂ : CoFree Exec N B}
    (h : Same RR t₁ t₂) : Same RR (skip n t₁) t₂ := by
  induction n generalizing t₁ with
  | zero => exact h
  | succ n ih =>
    unfold skip
    split
    next t' ht => exact ih (Same.silentL_inv h ht)
    next => exact h

theorem skipR_inv (n : Nat) {N : NonDeterminism} {t₁ : CoFree Exec N A} {t₂ : CoFree Exec SirND B}
    (h : Same RR t₁ t₂) : Same RR t₁ (skip n t₂) := by
  induction n generalizing t₂ with
  | zero => exact h
  | succ n ih =>
    unfold skip
    split
    next t' ht => exact ih (Same.silentR_inv h ht)
    next => exact h

/-! ## Programs -/

def prog (blocks : Array Block) : Program :=
  { init := 0, main := none, functions := #[⟨0, .never, blocks⟩] }

def run (p : Program) : CoFree Exec SirND Empty :=
  exec p noLayout (Immutables.ofWords p #[]) testEnv .init default

/-- The storage a run from the default state commits after storing `v` at `k`. -/
def stored (k v : Word) : Store := ⟨(default : Storage).set k v, default⟩

/-- `stop`, which the host hands on as `ret` with no data. -/
abbrev stopOp (st : Store) : WorldOp := .ret .empty st

theorem stop_ne {a b : Store} (k : Word) (h : a.storage k ≠ b.storage k) : stopOp a ≠ stopOp b :=
  fun e => h (by cases e; rfl)

def stops : Program := prog #[{ control := .stop }]

/-- Allocates, computes with the pointer, and never observes it. -/
def mallocs : Program := prog #[
  { ops := #[.let 1 (.const 32), .let 2 (.malloc 1), .let 3 (.binop .add 2 2)], control := .stop }]

def mallocsAny : Program := prog #[
  { ops := #[.let 1 (.const 64), .let 2 (.mallocany 1)], control := .stop }]

def stores (v : Word) : Program := prog #[
  { ops := #[.let 1 (.const 0), .let 2 (.const v), .stmt (.sstore 1 2)], control := .stop }]

/-- `stores 1` after a jump, which is one more silent step. -/
def jumpsThenStores : Program := prog #[
  { control := .continuesTo 1 },
  { ops := #[.let 1 (.const 0), .let 2 (.const 1), .stmt (.sstore 1 2)], control := .stop }]

/-- `stores 1` after reading the environment, which is not a host operation. -/
def readsEnvThenStores : Program := prog #[
  { ops := #[.let 1 (.const 0), .let 2 (.const 1), .let 3 (.query .caller),
      .let 4 (.calldataload 1), .let 5 (.blockhash 1), .stmt (.sstore 1 2)], control := .stop }]

/-- `sstore 0 5`, then `sstore 1 (sload 0)`. -/
def storeLoads : Program := prog #[
  { ops := #[.let 1 (.const 0), .let 2 (.const 5), .stmt (.sstore 1 2), .let 3 (.sload 1),
      .let 4 (.const 1), .stmt (.sstore 4 3)], control := .stop }]

/-- Stores the pointer it allocated. -/
def leaks : Program := prog #[
  { ops := #[.let 1 (.const 32), .let 2 (.malloc 1), .let 3 (.const 0), .stmt (.sstore 3 2)],
    control := .stop }]

/-- UB `switchNoMatch`. -/
def switchUB : Program := prog #[
  { ops := #[.let 1 (.const 5)], control := .switch 1 #[(0, 0)] none }]

/-- Malformed: `sstore`s an undefined variable. -/
def undefinedVar : Program := prog #[{ ops := #[.stmt (.sstore 1 1)], control := .stop }]

/-- Halts exceptionally, as invalid EVM code does. -/
def halts : Program := prog #[{ control := .invalid }]

/-- UB `memoryOutOfBounds`: reads memory that was never allocated. -/
def readUB : Program := prog #[
  { ops := #[.let 1 (.const 0), .let 2 (.mload ⟨32, by decide⟩ 1)], control := .stop }]

/-! ## Equivalent -/

/-- Placements are answered independently on each side, and the pointer is never observed. -/
theorem mallocs_same_mallocsAny : Same Eq (run mallocs) (run mallocsAny) := by
  apply same_skipL 100; apply same_skipR 100
  refine Same.branch (observe_of_headBr (c := .placement 32 [] ⟨0, by decide⟩) (by kernel_rfl))
    (observe_of_headBr (c := .placement 64 [] ⟨0, by decide⟩) (by kernel_rfl)) fun r₁ r₂ => ?_
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp default) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

/-- An allocation on one side only is skipped like any silent step. -/
theorem mallocs_same_stops : Same Eq (run mallocs) (run stops) := by
  apply same_skipL 100; apply same_skipR 100
  refine Same.branchL _ (observe_of_headBr (c := .placement 32 [] ⟨0, by decide⟩) (by kernel_rfl))
    fun r => ?_
  apply same_skipL 100
  exact Same.impure (op := stopOp default) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

theorem mallocs_deterministic : Deterministic (run mallocs) :=
  (Deterministic.of_same mallocs_same_stops).1

/-- What a compiler may emit for `mallocs`: it stops, with no allocation and so no choice. -/
def stopsTarget : CoFree Exec .none Empty := CoFree.impure (stopOp default) nofun

/-- A run with nondeterminism relates to one without: only operations are compared. -/
theorem mallocs_same_stopsTarget : Same Eq (run mallocs) stopsTarget := by
  apply same_skipL 100
  refine Same.branchL _ (observe_of_headBr (c := .placement 32 [] ⟨0, by decide⟩) (by kernel_rfl))
    fun r => ?_
  apply same_skipL 100
  exact Same.impure (op := stopOp default) (observe_of_headOp (by kernel_rfl)) rfl
    fun r => Empty.elim r

theorem stores_same_jumpsThenStores : Same Eq (run (stores 1)) (run jumpsThenStores) := by
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp (stored 0 1)) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

theorem stores_same_readsEnvThenStores : Same Eq (run (stores 1)) (run readsEnvThenStores) := by
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := stopOp (stored 0 1)) (observe_of_headOp (by kernel_rfl))
    (observe_of_headOp (by kernel_rfl)) fun r => Empty.elim r

/-- Undefined behavior relates to the same undefined behavior. -/
theorem switchUB_same_switchUB : Same Eq (run switchUB) (run switchUB) := by
  apply same_skipL 100; apply same_skipR 100
  exact Same.impure (op := .ub .switchNoMatch)
    (observe_of_headOp (by kernel_rfl)) (observe_of_headOp (by kernel_rfl)) nofun

/-! ## Not equivalent -/

theorem stores_not_same : ¬Same Eq (run (stores 1)) (run (stores 2)) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact stop_ne 0 (by decide) (Same.impure_inv h (observe_of_headOp (op := stopOp (stored 0 1))
    (by kernel_rfl)) (observe_of_headOp (op := stopOp (stored 0 2)) (by kernel_rfl)))

theorem switchUB_not_same_stops : ¬Same Eq (run switchUB) (run stops) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  nomatch Same.impure_inv h (observe_of_headOp (op := .ub .switchNoMatch) (by kernel_rfl))
    (observe_of_headOp (op := stopOp default) (by kernel_rfl))

/-- Undefined behavior of different kinds is not related: their payloads differ. -/
theorem switchUB_not_same_readUB : ¬Same Eq (run switchUB) (run readUB) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  have := Same.impure_inv h (observe_of_headOp (op := .ub .switchNoMatch) (by kernel_rfl))
    (observe_of_headOp (op := .ub (.memoryOutOfBounds 0 32)) (by kernel_rfl))
  simp at this

/-- A malformed program is UB, not related to a valid exceptional halt. -/
theorem undefinedVar_not_same_halts : ¬Same Eq (run undefinedVar) (run halts) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  nomatch Same.impure_inv h (observe_of_headOp (op := .ub .malformed) (by kernel_rfl))
    (observe_of_headOp (op := .invalid) (by kernel_rfl))

/-- `Same` is not reflexive: a run that stores a pointer depends on where it was placed. -/
theorem leaks_not_deterministic : ¬Deterministic (run leaks) := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 h)
  have h := Same.branchL_inv h
    (observe_of_headBr (c := .placement 32 [] ⟨0, by decide⟩) (by kernel_rfl)) ⟨0, by decide⟩
  have h := Same.branchR_inv h
    (observe_of_headBr (c := .placement 32 [] ⟨0, by decide⟩) (by kernel_rfl)) ⟨32, by decide⟩
  have h := skipR_inv 100 (skipL_inv 100 h)
  exact stop_ne 0 (by decide) (Same.impure_inv h (observe_of_headOp (op := stopOp (stored 0 0))
    (by kernel_rfl)) (observe_of_headOp (op := stopOp (stored 0 32)) (by kernel_rfl)))

end SirTests.Same
