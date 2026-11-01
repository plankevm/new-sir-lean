import Host
import ITree.Effect
import ITree.Machine
import Sir.Ir


namespace Sir

open CoFree

inductive UB
  | malformed (reason : String)
  | switchNoMatch
  | illegalOverflow
  | memoryOutOfBounds (offset length : Nat)
  | uninitializedRead (offset length : Nat)
  | outOfMemory (size : Nat)
  deriving DecidableEq, Repr

structure MemCopy where
  dst : Word
  src : Word
  length : Word

inductive SirOp
  | alloc (zeroed : Bool) (size : Word)
  | read (offset length : Word)
  | write (offset : Word) (bytes : ByteArray)
  | copy (copy : MemCopy)
  | ub (ub : UB)

def SirOp.Resp : SirOp → Type
  | .alloc .. => Word
  | .read .. => ByteArray
  | .write .. => Unit
  | .copy .. => Unit
  | .ub _ => Empty


abbrev SirE : Effect := ⟨SirOp, SirOp.Resp⟩

/-- `[start, start + size)` fits in the address space and misses every live allocation `(start, size)`. -/
def Placement (a' : NatRange) (live : List NatRange) : Prop :=
  a'.end ≤ Word.size ∧ ∀ a ∈ live, a.Disjoint a'

instance (live : List NatRange) (a' : NatRange) : Decidable (Placement a' live) := by
  unfold Placement; infer_instance

instance {live : List NatRange} {size : Nat} : Decidable (∃ start, Placement ⟨start, size⟩ live) :=
  if h : ∃ start ∈ 0 :: live.map (·.end), Placement ⟨start, size⟩ live
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

inductive Choice
  | placement (size : Nat) (live : List NatRange) (fits : ∃ start, Placement ⟨start, size⟩ live)
  deriving DecidableEq

def Choice.Resp : Choice → Type
  | .placement size live _ => { start : Nat // Placement ⟨start, size⟩ live }

abbrev SirND : NonDeterminism where
  Op := Choice
  Resp := Choice.Resp
  resp_nonempty
    | .placement _ _ ⟨start, h⟩ => ⟨⟨start, h⟩⟩

end Sir
