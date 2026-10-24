import Sir.Memory
import ITree.Same

/-! How a run ends, and which runs are safe.

A run of `exec` has type `CoFree Exec Empty`: it never returns a value, it ends with a terminal
host operation (the EVM halts, or a fault). So that operation is its final result.

Runs are compared with `CoFree.Same` after `Mem` is handled. Allocations are then branches
(`Choice.placement`), unobserved steps of `Same`: each is answered with every valid placement, on
each side independently, and the runs must agree for every pair of placements. Every host
operation is visible and must match exactly, in the same order. A fault (`fault (.ub u)`,
`fault .malformed`) has no answer, so it ends the run and relates only to the same fault; in
particular undefined behavior of different kinds, or with different arguments (which may mention
placement-dependent addresses), is not related. A run whose visible behavior depends on where
something was allocated (say it stores a pointer) is not `CoFree.Deterministic`. -/

namespace Sir

inductive Outcome
  | stop
  | ret (data : ByteArray)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Word)
  | fault (f : Fault)
  deriving DecidableEq

/-- The terminal host operation that ends a run with this outcome. -/
def Outcome.op : Outcome → HostOp
  | .stop => .stop
  | .ret data => .ret data
  | .revert data => .revert data
  | .invalid => .invalid
  | .selfdestruct a => .selfdestruct a
  | .fault f => .fault f

/-- `t` ends with `o` for some answers to its host operations and some placements, after finitely
many steps. -/
inductive HasOutcome : CoFree Exec Empty → Outcome → Prop
  | halt {t o k} :
      t.observe = .impure o.op k →
        HasOutcome t o
  | silent {t t' o} :
      t.observe = .silent t' →
      HasOutcome t' o →
        HasOutcome t o
  | branch {t c k o} (r : Choice.Resp c) :
      t.observe = .branch c k →
      HasOutcome (k r) o →
        HasOutcome t o
  | impure {t op k o} (r : HostOp.Resp op) :
      t.observe = .impure op k →
      HasOutcome (k r) o →
        HasOutcome t o

/-- `t` reaches no undefined behavior, and does not depend on where its allocations are placed.
The second half is not implied by the first: a run returning a pointer it allocated has no UB
outcome, but different placements give it different outcomes. -/
def Safe (t : CoFree Exec Empty) : Prop :=
  (∀ u, ¬HasOutcome t (.fault (.ub u))) ∧ CoFree.Deterministic t

/-- An entry point is safe for every frame environment (calldata, caller, …) and every value of
the immutables. The layout is fixed by the compiler, so it is a parameter. -/
def Program.Safe (p : Program) (layout : Layout) (e : Entry) : Prop :=
  ∀ imm env, Sir.Safe (exec p layout imm env e)

end Sir
