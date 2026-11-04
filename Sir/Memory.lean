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


namespace MemState

def allocAt? (m : MemState) (addr : Nat) : Option Allocation :=
  m.find? fun a => a.start.toNat ≤ addr && addr < a.end

def read? (m : MemState) (offset length : Nat) : Option ByteArray :=
  (Array.range length).mapM (fun i => (m.allocAt? (offset + i)).map fun a =>
    a.bytes.get! (offset + i - a.start.toNat)) |>.map (⟨·⟩)

def inBounds (m : MemState) (offset length : Nat) : Bool :=
  (List.range length).all fun i => (m.allocAt? (offset + i)).isSome

def write (m : MemState) (offset : Nat) (bytes : ByteArray) : MemState :=
  (List.range bytes.size).foldl (init := m) fun m i =>
    let addr := offset + i
    m.map fun a => if a.start.toNat ≤ addr && addr < a.end
      then { a with bytes := a.bytes.set! (addr - a.start.toNat) (bytes.get! i) } else a

end MemState

/-- Handles `SirE` with a list of allocations; placements are branches of `MemoryND`, so an
uninitialized allocation's bytes are whatever the branch picked. Undefined behavior is returned,
not performed: `HostE` has no operation for it.

The loop's mutable state is the program itself, so this machine lives one universe up. -/
def interpMem {α : Type} (sir : SirM α) : CoFree HostE MemoryND (ULift.{1} (Except UB α)) := do
  let mut sir := sir
  let mut mem : MemState := #[]
  repeat
    match sir.observe with
    | .pure a => return ⟨.ok a⟩
    | .silent sir' => sir := sir'
    | .impure (.inl op) k =>
      let ⟨r⟩ ← (perform (E := HostE) (N := MemoryND) op).up
      sir := k r
    | .impure (.inr (.alloc zeroed size)) k =>
      let ⟨⟨pick, valid⟩⟩ ← (CoFree.branch (E := HostE) (N := MemoryND) (.alloc size mem.toList)).up
      match pick, valid with
      | none, _ => return ⟨.error (.outOfMemory size.toNat)⟩
      | some a, _ =>
        let a := if zeroed then { a with bytes := ⟨.replicate a.size 0⟩ } else a
        mem := mem.push a
        sir := k a.start
    | .impure (.inr (.read offset length)) k =>
      let some bytes := mem.read? offset.toNat length.toNat
        | return ⟨.error (.memoryOutOfBounds offset.toNat length.toNat)⟩
      sir := k bytes
    | .impure (.inr (.write offset bytes)) k =>
      unless mem.inBounds offset.toNat bytes.size do
        return ⟨.error (.memoryOutOfBounds offset.toNat bytes.size)⟩
      mem := mem.write offset.toNat bytes
      sir := k ()
    | .impure (.inr (.copy ⟨dst, src, length⟩)) k =>
      let some bytes := mem.read? src.toNat length.toNat
        | return ⟨.error (.memoryOutOfBounds src.toNat length.toNat)⟩
      unless mem.inBounds dst.toNat length.toNat do
        return ⟨.error (.memoryOutOfBounds dst.toNat length.toNat)⟩
      mem := mem.write dst.toNat bytes
      sir := k ()
    | .impure (.inr (.ub u)) _ => return ⟨.error u⟩
    | .branch c _ => nomatch c
  CoFree.spin


end Sir
