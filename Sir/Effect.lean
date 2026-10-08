import ITree
import Sir.Ir

/-! The effects of a SIR run.

The evaluator emits `SirE = Mem ⊕ₑ Host`. `Mem` (allocation, byte reads/writes, the return
data buffer) is frame-local and handled by `Sir.Memory`; `Host` is everything else and stays
abstract: the EVM, the world and the bytecode an entry point runs as. -/

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

inductive HostOp
  | query (q : Query)
  | balance (account : Word)
  | extcodehash (account : Word)
  | blockhash (number : Word)
  | blobhash (index : Word)
  | sload (key : Word)
  | tload (key : Word)
  | sstore (key value : Word)
  | tstore (key value : Word)
  | calldata
  | code
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

def HostOp.Resp : HostOp → Type
  | .query _ | .balance _ | .extcodehash _ | .blockhash _ | .blobhash _ => Word
  | .sload _ | .tload _ => Word
  | .sstore .. => Unit
  | .tstore .. => Unit
  | .calldata => ByteArray
  | .code => ByteArray
  | .extcode _ => ByteArray
  | .log .. => Unit
  | .call .. => Bool × ByteArray
  | .create .. => Word × ByteArray
  | .alloc size live => { start : Nat // Placement live size start }
  | .stop => Empty
  | .ret _ => Empty
  | .revert _ => Empty
  | .invalid => Empty
  | .selfdestruct _ => Empty
  | .fault _ => Empty

abbrev Host : Effect := ⟨HostOp, HostOp.Resp⟩

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

abbrev Mem : Effect := ⟨MemOp, MemOp.Resp⟩

abbrev SirE : Effect := Mem ⊕ₑ Host

end Sir
