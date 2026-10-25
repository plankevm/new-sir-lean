import ITree
import Sir.Ir

/-! The effects of a SIR run.

The evaluator reads `Env` and emits `SirE = Mem ⊕ₑ Host`. `Env` holds what stays fixed for the
whole frame, so reading it is pure: equivalence can ignore, reorder or drop those reads. `Mem`
(allocation, byte reads/writes, the return data buffer) is frame-local and handled by
`Sir.Memory`; `Host` is everything that can change during the frame and stays abstract: gas,
balances, other accounts, storage, calls and logs. Handling `Mem` leaves `Exec`: the `Host`
operations, plus a branch (`Choice`) wherever an allocation is placed. -/

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

structure MemRange where
  start : Nat
  size : Nat
  deriving DecidableEq

namespace MemRange

def «end» (a : MemRange) : Nat := a.start + a.size

def Disjoint (a₁ a₂ : MemRange) : Prop := a₁.end ≤ a₂.start ∨ a₂.end ≤ a₁.start

instance {a₁ a₂ : MemRange} : Decidable (a₁.Disjoint a₂) := by unfold Disjoint; infer_instance

/-- `[start, start + size)` fits in the address space and misses every live allocation `(start, size)`. -/
def Placement (a' : MemRange) (live : List MemRange) : Prop :=
  a'.end ≤ Word.size ∧ ∀ a ∈ live, a.Disjoint a'

instance (live : List MemRange) (a' : MemRange) : Decidable (Placement a' live) := by
  unfold Placement; infer_instance

universe u

instance {α : Type u} (p : α → Prop) (l : List α) [DecidablePred p] : Decidable (∃ x ∈ l, p x) := by
  infer_instance

instance {live : List MemRange} {size : Nat} : Decidable (∃ start, Placement ⟨start, size⟩ live) :=
  if h : ∃ start ∈ 0 :: live.map (fun a => a.end), Placement ⟨start, size⟩ live
  then .isTrue (let ⟨start, _, h⟩ := h; ⟨start, h⟩)
  else .isFalse fun ⟨start, hs⟩ => h <| by
    -- A placement at neither 0 nor a live end slides down by one and stays a placement.
    induction start with
    | zero => exact ⟨0, List.mem_cons_self, hs⟩
    | succ s ih =>
      if hc : s + 1 ∈ 0 :: live.map (fun a => a.end) then exact ⟨s + 1, hc, hs⟩
      else
        refine ih ⟨by have := hs.1; simp only [MemRange.end] at *; omega, fun a ha => ?_⟩
        have := hs.2 a ha
        have : a.end ≠ s + 1 := fun e => hc (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, ha, e⟩))
        simp only [Disjoint, MemRange.end] at *
        omega
    

end MemRange

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

/-- Where a new allocation of `size` bytes goes, among the placements that miss the `live`
allocations. Nobody controls the choice; it is made only when some placement exists. -/
inductive Choice
  | placement (size : Nat) (live : List MemRange) (fits : ∃ start, MemRange.Placement ⟨start, size⟩ live)
  deriving DecidableEq

def Choice.Resp : Choice → Type
  | .placement size live _ => { start : Nat // MemRange.Placement ⟨start, size⟩ live }

/-- What a run emits once `Mem` is handled. -/
abbrev Exec : Effect where
  Op := HostOp
  Resp := HostOp.Resp
  BrOp := Choice
  BrResp := Choice.Resp
  brResp_nonempty
    | .placement _ _ ⟨start, h⟩ => ⟨⟨start, h⟩⟩

end Sir
