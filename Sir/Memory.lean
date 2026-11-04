import Sir.Eval

open Host
open CoFree (perform)

namespace Sir

structure Allocation where
  start : Word
  bytes : ByteArray

def Allocation.size (a : Allocation) : Nat := a.bytes.size
def Allocation.range (a : Allocation) : NatRange := ⟨a.start.toNat, a.size⟩
def Allocation.end (a : Allocation) : Nat := a.start.toNat + a.size

def Allocation.contains (a : Allocation) (addr : Nat) : Prop := addr ∈ a.range

/-- `[start, start + size)` fits in the address space and misses every live allocation `(start, size)`. -/
def ValidAlloc  (live : List Allocation)  (size : Nat) : Allocation → Prop :=
  fun a' => a'.size = size ∧ a'.end ≤ Word.size ∧ ∀ a ∈ live, a.range.Disjoint a'.range

instance (live : List Allocation) (size : Nat) : DecidablePred (ValidAlloc live size) := by
  unfold ValidAlloc; infer_instance

inductive MemoryBranchOp
  | alloc (size : Word) (live : List Allocation)

universe u

def Pick (α : Type u) (p : α → Prop) :=
  Subtype (fun
    | some a => p a
    | none => ¬∃ a, p a
  )

instance {α : Type u} {p : α → Prop} : Nonempty (Pick α p) := by
  if h : ∃ a, p a
  then
    have ⟨a, ha⟩ := h
    exact ⟨⟨some a, ha⟩⟩
  else exact ⟨⟨none, h⟩⟩

abbrev MemoryND : NonDeterminism where
  Op := MemoryBranchOp
  Resp | .alloc size live => Pick Allocation (ValidAlloc live size.toNat)

abbrev MemState := Array Allocation


def interpMem {α : Type} (sir : SirM α) : CoFree HostE MemoryND α := do
  let mut sir := sir
  repeat
    match sir.observe with
    | _ => sorry


end Sir
