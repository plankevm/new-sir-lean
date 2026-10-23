import ITree
import Sir.Ir

/-! The effects of a SIR run.

The evaluator reads `Env` and emits `SirE = Mem ⊕ₑ Host`. `Env` holds what stays fixed for the
whole frame, so reading it is pure: equivalence can ignore, reorder or drop those reads. `Mem`
(allocation, byte reads/writes, the return data buffer) is frame-local and handled by
`Sir.Memory`; `Host` is everything that can change during the frame and stays abstract: gas,
balances, other accounts, storage, calls and logs. -/

namespace Sir

/-- Undefined behavior: well-formed programs can reach these, depending on the values they compute. -/
inductive UB
  | switchNoMatch
  | memoryOutOfBounds (offset length : Nat)
  | uninitializedRead (offset length : Nat)
  | outOfMemory (size : Nat)
  deriving DecidableEq, Repr

/-- Why a run is stuck. -/
inductive Fault
  | malformed
  | ub (u : UB)
  deriving DecidableEq, Repr

inductive CallKind
  | call (value : Word)
  | callcode (value : Word)
  | delegatecall
  | staticcall
  deriving DecidableEq, Repr

/-- `[start, start + size)` fits in the address space and misses every live allocation
`(start, size)`. -/
def Placement (live : List (Nat × Nat)) (size start : Nat) : Prop :=
  start + size ≤ 2 ^ 256 ∧ ∀ a ∈ live, start + size ≤ a.1 ∨ a.1 + a.2 ≤ start

instance (live : List (Nat × Nat)) (size start : Nat) : Decidable (Placement live size start) := by
  unfold Placement; infer_instance

/-- The frame's constants: the transaction, the block, and the code being run. -/
structure Env where
  address : Word
  origin : Word
  caller : Word
  callvalue : Word
  gasprice : Word
  chainid : Word
  coinbase : Word
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

inductive HostOp
  | gas
  | selfbalance
  | balance (account : Word)
  | extcodehash (account : Word)
  | sload (key : Word)
  | tload (key : Word)
  | sstore (key value : Word)
  | tstore (key value : Word)
  | extcode (account : Word)
  | log (topics : Array Word) (data : ByteArray)
  | call (kind : CallKind) (gas account : Word) (input : ByteArray)
  | create (value : Word) (salt : Option Word) (initcode : ByteArray)
  | alloc (size : Nat) (live : List (Nat × Nat))
  | stop
  | ret (data : ByteArray)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Word)
  | fault (fault : Fault)
  deriving DecidableEq

def HostOp.Resp : HostOp → Type
  | .gas | .selfbalance | .balance _ | .extcodehash _ => Word
  | .sload _ | .tload _ => Word
  | .sstore .. | .tstore .. => Unit
  | .extcode _ => ByteArray
  | .log .. => Unit
  | .call .. => Bool × ByteArray
  | .create .. => Word × ByteArray
  | .alloc size live => { start : Nat // Placement live size start }
  | .stop | .ret _ | .revert _ | .invalid | .selfdestruct _ => Empty
  | .fault _ => Empty

abbrev Host : Effect := { Op := HostOp, Resp := HostOp.Resp }

inductive MemOp
  | alloc (zeroed : Bool) (size : Nat)
  | read (offset length : Nat)
  | write (offset : Nat) (bytes : ByteArray)
  | copy (dst src length : Nat)
  | returnData
  | setReturnData (bytes : ByteArray)

def MemOp.Resp : MemOp → Type
  | .alloc .. => Word
  | .read .. => ByteArray
  | .write .. => Unit
  | .copy .. => Unit
  | .returnData => ByteArray
  | .setReturnData _ => Unit

abbrev Mem : Effect := { Op := MemOp, Resp := MemOp.Resp }

abbrev SirE : Effect := Mem ⊕ₑ Host

end Sir
