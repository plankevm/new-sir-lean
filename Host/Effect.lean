import ITree
import Host.Word
import Host.NatRange

/-! The EVM host interface of one call frame, shared by every IR that compiles to the EVM.

`Env` holds what stays fixed for the whole frame, so reading it is pure. `HostE` is everything
else the frame asks of the outside: gas, its own storage and transient storage, the rest of the
world (balances, code), calls, creations, logs, and how the frame ends. It is the same for every
IR, so runs of different IRs can be related. A frame ends normally (`stop`, `ret`,
`selfdestruct`), by reverting, by an exceptional halt (`invalid`: every EVM exceptional halt
looks the same from outside), or with undefined behavior (`ub`), which an IR may reach and the
EVM never does; a malformed IR program is UB, never a valid halt. Its branches (`Choice`) are the choices nobody controls: where an allocation is placed, or one
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


/-- `[start, start + size)` fits in the address space and misses every live allocation `(start, size)`. -/
def Placement (a' : NatRange) (live : List NatRange) : Prop :=
  a'.end ≤ Word.size ∧ ∀ a ∈ live, a.Disjoint a'

instance (live : List NatRange) (a' : NatRange) : Decidable (Placement a' live) := by
  unfold Placement; infer_instance

universe u

instance {α : Type u} (p : α → Prop) (l : List α) [DecidablePred p] : Decidable (∃ x ∈ l, p x) := by
  infer_instance

instance {live : List NatRange} {size : Nat} : Decidable (∃ start, Placement ⟨start, size⟩ live) :=
  if h : ∃ start ∈ 0 :: live.map (fun a => a.end), Placement ⟨start, size⟩ live
  then .isTrue (let ⟨start, _, h⟩ := h; ⟨start, h⟩)
  else .isFalse fun ⟨start, hs⟩ => h <| by
    -- A placement at neither 0 nor a live end slides down by one and stays a placement.
    induction start with
    | zero => exact ⟨0, List.mem_cons_self, hs⟩
    | succ s ih =>
      if hc : s + 1 ∈ 0 :: live.map (fun a => a.end) then exact ⟨s + 1, hc, hs⟩
      else
        refine ih ⟨by have := hs.1; simp only [NatRange.end] at *; omega, fun a ha => ?_⟩
        have := hs.2 a ha
        have : a.end ≠ s + 1 := fun e => hc (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, ha, e⟩))
        simp only [NatRange.Disjoint, NatRange.end] at *
        omega

/-- Undefined behavior: `malformed` for an ill-formed IR program, the rest reachable by well-formed
programs depending on the values they compute. -/
inductive UB
  | malformed
  | switchNoMatch
  | memoryOutOfBounds (offset length : Nat)
  | uninitializedRead (offset length : Nat)
  | outOfMemory (size : Nat)
  deriving DecidableEq, Repr

/-- A choice nobody controls. `placement`: where a new allocation of `size` bytes goes, among
the placements that miss the `live` allocations; made only when some placement exists.
`choose n`: one of `n` alternatives. -/
inductive Choice
  | placement (size : Nat) (live : List NatRange) (fits : ∃ start, Placement ⟨start, size⟩ live)
  | choose (n : Nat) (pos : 0 < n)
  deriving DecidableEq

def Choice.Resp : Choice → Type
  | .placement size live _ => { start : Nat // Placement ⟨start, size⟩ live }
  | .choose n _ => Fin n

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

abbrev HostE : Effect where
  Op := HostOp
  Resp := HostOp.Resp
  BrOp := Choice
  BrResp := Choice.Resp
  brResp_nonempty
    | .placement _ _ ⟨start, h⟩ => ⟨⟨start, h⟩⟩
    | .choose _ pos => ⟨⟨0, pos⟩⟩

end Host
