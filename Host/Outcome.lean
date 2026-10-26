import Host.Storage
import ITree.Same

/-! How a run ends, and which runs are safe.

A run has type `CoFree WorldE Empty`: it never returns a value, it ends with a terminal
operation (the frame halts, or undefined behavior). So that operation is its final result. Every
IR's runs have this type once their own effects are handled, so these notions are shared.

Runs are compared with `CoFree.Same`. Branches (`Choice`) are unobserved steps of `Same`: each
is answered with every possible response, on each side independently, and the runs must agree
for every pair of responses. Every operation (gas, logs, calls, creations, the end of the run)
is visible and must match exactly, in the same order. A terminal operation has no answer, so
it ends the run and relates only to the same operation; in particular undefined behavior of
different kinds, or with different arguments (which may mention placement-dependent addresses),
is not related. A run whose visible behavior depends on a branch (say it stores a pointer whose
placement was a branch) is not `CoFree.Deterministic`. -/

namespace Host

/-- How a run ends. A run that commits (`ret`, `selfdestruct`) ends with the running account's
storage and transient storage. -/
inductive Outcome
  | ret (data : ByteArray) (store : Store)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Address) (store : Store)
  | ub (u : UB)

/-- The outcome of a run ending with `op`. Only operations without an answer end a run; listing
every operation makes a new one decide which it is. -/
def Outcome.ofOp : (op : WorldOp) → (WorldOp.Resp op → False) → Outcome
  | .gas, h => (h (0 : Word)).elim
  | .log .., h => (h ()).elim
  | .call .staticcall .., h => (h (false, .empty)).elim
  | .call (.call _) .., h | .call (.callcode _) .., h | .call .delegatecall .., h =>
    (h (false, .empty, default)).elim
  | .create .., h => (h (0, .empty, default)).elim
  | .ret data st, _ => .ret data st
  | .revert data, _ => .revert data
  | .invalid, _ => .invalid
  | .selfdestruct a st, _ => .selfdestruct a st
  | .ub u, _ => .ub u

/-- `t` ends with `o` for some answers to its operations and some branches, after finitely
many steps. -/
inductive HasOutcome : CoFree WorldE Empty → Outcome → Prop
  | halt {t op k} (h : WorldOp.Resp op → False) :
      t.observe = .impure op k →
        HasOutcome t (.ofOp op h)
  | silent {t t' o} :
      t.observe = .silent t' →
      HasOutcome t' o →
        HasOutcome t o
  | branch {t c k o} (r : Choice.Resp c) :
      t.observe = .branch c k →
      HasOutcome (k r) o →
        HasOutcome t o
  | impure {t op k o} (r : WorldOp.Resp op) :
      t.observe = .impure op k →
      HasOutcome (k r) o →
        HasOutcome t o

/-- `t` reaches no undefined behavior, and does not depend on its branches (say, where its
allocations are placed). The second half is not implied by the first: a run returning a pointer
it allocated has no UB outcome, but different placements give it different outcomes. -/
def Safe (t : CoFree WorldE Empty) : Prop :=
  (∀ u, ¬HasOutcome t (.ub u)) ∧ CoFree.Deterministic t

end Host
