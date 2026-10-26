import ITree
import Host.Word

/-! The EVM host interface of one call frame, shared by every IR that compiles to the EVM.

`Env` holds what stays fixed for the whole frame, so reading it is pure. `HostE Φ` is everything
else the frame asks of the outside: gas, its own storage and transient storage, the rest of the
world (balances, code), calls, creations, logs, and how the frame ends. `Φ` is the IR's own
reason for a run to be stuck (malformed program, undefined behavior); a `fault` ends the run.
Its branches (`Choice`) are the choices nobody controls: where an allocation is placed, or one
of `n` alternatives (say, which ready node of a dataflow graph runs next). `Host.Storage` makes
storage and the world concrete. -/

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
  static : Bool

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

/-- A choice nobody controls. `placement`: where a new allocation of `size` bytes goes, among
the placements that miss the `live` allocations; made only when some placement exists.
`choose n`: one of `n` alternatives. -/
inductive Choice
  | placement (size : Nat) (live : List MemRange) (fits : ∃ start, MemRange.Placement ⟨start, size⟩ live)
  | choose (n : Nat) (pos : 0 < n)
  deriving DecidableEq

def Choice.Resp : Choice → Type
  | .placement size live _ => { start : Nat // MemRange.Placement ⟨start, size⟩ live }
  | .choose n _ => Fin n

inductive HostOp (Φ : Type)
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
  | fault (fault : Φ)
  deriving DecidableEq

def HostOp.Resp {Φ : Type} : HostOp Φ → Type
  | .gas | .selfbalance | .balance _ | .extcodehash _ => Word
  | .sload _ | .tload _ => Word
  | .sstore .. | .tstore .. => Unit
  | .extcode _ => ByteArray
  | .log .. => Unit
  | .call .. => Bool × ByteArray
  | .create .. => Word × ByteArray
  | .stop | .ret _ | .revert _ | .invalid | .selfdestruct _ => Empty
  | .fault _ => Empty

abbrev HostE (Φ : Type) : Effect where
  Op := HostOp Φ
  Resp := HostOp.Resp
  BrOp := Choice
  BrResp := Choice.Resp
  brResp_nonempty
    | .placement _ _ ⟨start, h⟩ => ⟨⟨start, h⟩⟩
    | .choose _ pos => ⟨⟨0, pos⟩⟩

end Host
