import ITree
import Sir.Ir

/-! The effects of a SIR run.

The evaluator emits `SirE = Mem ⊕ₑ Host`. `Mem` (allocation, byte reads/writes, the return
data buffer) is frame-local and handled by `Sir.Memory`; `Host` is everything else and stays
abstract: the EVM, the world and the bytecode an entry point runs as. -/

namespace Sir

/-- A run of a malformed program got stuck. A well-formed program never reaches any of these. -/
inductive Malformed
  | undefinedVariable (var : VarId)
  | invalidFunction (function : FunctionId)
  | invalidBlock (block : BlockId)
  | invalidData (data : DataId)
  | invalidImmutable (immutable : ImmutableId)
  | arity (expected actual : Nat)
  | badOperands (op : EvmOp) (count : Nat)
  | fellThrough (block : BlockId)
  | returnKindMismatch (function : FunctionId)
  | neverReturned (function : FunctionId)
  | entryReturned
  | noMain
  | wrongEntry
  deriving DecidableEq, Repr

/-- Undefined behavior: well-formed programs can reach these, depending on the values they compute. -/
inductive UB
  | switchNoMatch
  | memoryOutOfBounds (offset length : Nat)
  | uninitializedRead (offset length : Nat)
  | outOfMemory (size : Nat)
  deriving DecidableEq, Repr

/-- Why a run is stuck. -/
inductive Fault
  | malformed (m : Malformed)
  | ub (u : UB)
  deriving DecidableEq, Repr

/-- Word-valued reads of the environment, the world and the deployed code. -/
inductive Query
  | address | balance (account : Word) | origin | caller | callvalue | gasprice
  | extcodehash (account : Word) | gas
  | blockhash (number : Word) | coinbase | timestamp | number | prevrandao | gaslimit | chainid
  | selfbalance | basefee | blobhash (index : Word) | blobbasefee
  | sload (key : Word) | tload (key : Word)
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
  | sstore (key value : Word)
  | tstore (key value : Word)
  | calldata
  | code
  | extcode (account : Word)
  | log (topics : List Word) (data : ByteArray)
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
  | .query _ => Word
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
