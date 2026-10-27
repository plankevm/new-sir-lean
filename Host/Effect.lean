import ITree
import Host.Word

/-! The EVM host interface of one call frame, shared by every IR that compiles to the EVM.

`Env` holds what stays fixed for the whole frame, so reading it is pure. `HostE` is everything
else the frame asks of the outside: gas, its own storage and transient storage, the rest of the
world (balances, code), calls, creations, logs, and how the frame ends. It is the same for every
IR, so runs of different IRs can be related. A frame ends normally (`stop`, `ret`,
`selfdestruct`), by reverting, by an exceptional halt (`invalid`: every EVM exceptional halt
looks the same from outside), or with undefined behavior (`ub`), which an IR may reach and the
EVM never does; a malformed IR program is UB, never a valid halt. `Host.Storage` makes storage
and the world concrete.

The host has no nondeterminism of its own: an IR's choices (say, where SIR places an allocation)
are its own `NonDeterminism`, which every handler here passes through untouched. -/

namespace Host

inductive CallKind
  | call (value : Word)
  | callcode (value : Word)
  | delegatecall
  | staticcall
  deriving DecidableEq, Repr

/-- The frame's constants: the transaction, the block, the code being run, and whether the frame
may change state. -/
structure Env where
  address : Address
  origin : Address
  caller : Address
  callvalue : Word
  gasprice : Word
  chainid : Word
  coinbase : Address
  timestamp : Word
  number : Word
  prevrandao : Word
  gaslimit : Word
  basefee : Word
  blobbasefee : Word
  blockhash : Word → Word
  blobhash : Word → Word
  calldata : ByteArray
  code : ByteArray
  static : Bool

structure MemRange where
  start : Nat
  size : Nat
  deriving DecidableEq

namespace MemRange

def «end» (a : MemRange) : Nat := a.start + a.size

def Disjoint (a₁ a₂ : MemRange) : Prop := a₁.end ≤ a₂.start ∨ a₂.end ≤ a₁.start

theorem Disjoint_imp_no_overlap : ∀ a₁ a₂, (Disjoint a₁ a₂) → (¬∃ x, a₁.start ≤ x ∧ x < a₁.end ∧
a₂.start ≤ x ∧ x < a₂.end) := by
  unfold Disjoint
  intro disjoint
  grind

theorem no_overlap_imp_Disjoint_or_empty :
  ∀ a₁ a₂, (¬∃ x, a₁.start ≤ x ∧ x < a₁.end ∧ a₂.start ≤ x ∧ x < a₂.end) →
    (Disjoint a₁ a₂ ∨ a₁.size = 0 ∨ a₂.size = 0) := by
  unfold Disjoint
  intro a₁ a₂ no_overlap
  refine Classical.byContradiction fun h => ?_
  exact no_overlap ⟨max a₁.start a₂.start, by simp only [MemRange.end] at *; omega⟩

instance {a₁ a₂ : MemRange} : Decidable (a₁.Disjoint a₂) := by unfold Disjoint; infer_instance

end MemRange

/-- Undefined behavior: `malformed` for an ill-formed IR program, the rest reachable by well-formed
programs depending on the values they compute. -/
inductive UB
  | malformed
  | switchNoMatch
  | memoryOutOfBounds (offset length : Nat)
  | uninitializedRead (offset length : Nat)
  | outOfMemory (size : Nat)
  deriving DecidableEq, Repr

inductive HostOp
  | gas
  | selfbalance
  | balance (account : Address)
  | extcodehash (account : Address)
  | sload (key : Word)
  | tload (key : Word)
  | sstore (key value : Word)
  | tstore (key value : Word)
  | extcode (account : Address)
  | log (topics : Array Word) (data : ByteArray)
  | call (kind : CallKind) (gas : Word) (account : Address) (input : ByteArray)
  | create (value : Word) (salt : Option Word) (initcode : ByteArray)
  | stop
  | ret (data : ByteArray)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Address)
  | ub (u : UB)
  deriving DecidableEq

def HostOp.Resp : HostOp → Type
  | .gas | .selfbalance | .balance _ | .extcodehash _ => Word
  | .sload _ | .tload _ => Word
  | .sstore .. | .tstore .. => Unit
  | .extcode _ => ByteArray
  | .log .. => Unit
  | .call .. => Bool × ByteArray
  | .create .. => Address × ByteArray
  | .stop | .ret _ | .revert _ | .invalid | .selfdestruct _ | .ub _ => Empty

abbrev HostE : Effect := { Op := HostOp, Resp := HostOp.Resp }

end Host
