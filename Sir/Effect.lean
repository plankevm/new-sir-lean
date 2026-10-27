import Host
import Sir.Ir

/-! The effects of a SIR run.

The evaluator reads `Env` and emits `SirE = Mem ⊕ₑ HostE`, deterministically. `Env` holds what
stays fixed for the whole frame, so reading it is pure: equivalence can ignore, reorder or drop
those reads. `Mem` (allocation, byte reads/writes, the return data buffer) is frame-local and
handled by `Sir.Memory`, which places each allocation by a branch (`Choice.placement`): SIR's own
nondeterminism `SirND`. `HostE` is the shared EVM host interface (`Host.Effect`), which knows
nothing of `SirND` and passes it through; `Host.interpStore` then makes storage and the world
concrete, leaving `Exec`: gas, logs, calls, creations and the end of the frame. -/

namespace Sir

open Host

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

abbrev SirE : Effect := Mem ⊕ₑ HostE

/-- `[start, start + size)` fits in the address space and misses every live allocation `(start, size)`. -/
def Placement (a' : MemRange) (live : List MemRange) : Prop :=
  a'.end ≤ Word.size ∧ ∀ a ∈ live, a.Disjoint a'

instance (live : List MemRange) (a' : MemRange) : Decidable (Placement a' live) := by
  unfold Placement; infer_instance

instance {α : Type} (p : α → Prop) (l : List α) [DecidablePred p] : Decidable (∃ x ∈ l, p x) := by
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
        simp only [MemRange.Disjoint, MemRange.end] at *
        omega

/-- A choice nobody controls. `placement`: where a new allocation of `size` bytes goes, among
the placements that miss the `live` allocations; made only when some placement exists.
`choose n`: one of `n` alternatives. -/
inductive Choice
  | placement (size : Nat) (live : List MemRange) (fits : ∃ start, Placement ⟨start, size⟩ live)
  | choose (n : Nat) (pos : 0 < n)
  deriving DecidableEq

def Choice.Resp : Choice → Type
  | .placement size live _ => { start : Nat // Placement ⟨start, size⟩ live }
  | .choose n _ => Fin n

abbrev SirND : NonDeterminism where
  Op := Choice
  Resp := Choice.Resp
  resp_nonempty
    | .placement _ _ ⟨start, h⟩ => ⟨⟨start, h⟩⟩
    | .choose _ pos => ⟨⟨0, pos⟩⟩

/-- What a run emits once `Mem`, storage and the world are handled. -/
abbrev Exec : Effect := WorldE

end Sir
