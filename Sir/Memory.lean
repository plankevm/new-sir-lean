import Sir.Effect

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

private def zeroedAt (size start : Nat) : Allocation := ⟨Word.ofNat start, ⟨.replicate size 0⟩⟩

instance (live : List Allocation) (size : Nat) : Decidable (∃ a', ValidAlloc live size a') :=
  decidable_of_iff (∃ s ∈ (0 : Nat) :: live.map Allocation.end, s < Word.size ∧
      s + size ≤ Word.size ∧ ∀ a ∈ live, a.range.Disjoint ⟨s, size⟩) <| by
    have valid {t} (ht : t < Word.size) : ValidAlloc live size (zeroedAt size t) ↔
        t + size ≤ Word.size ∧ ∀ a ∈ live, a.range.Disjoint ⟨t, size⟩ := by
      have : (Word.ofNat t).toNat = t := Nat.mod_eq_of_lt ht
      have hsz : (⟨.replicate size 0⟩ : ByteArray).size = size := by simp [ByteArray.size]
      simp [ValidAlloc, Allocation.range, Allocation.end, Allocation.size, zeroedAt, hsz, this]
    refine ⟨fun ⟨_, _, ht, h⟩ => ⟨_, (valid ht).2 h⟩, fun ⟨a', hsize, hfit, hdisj⟩ => ?_⟩
    have hlt : a'.start.toNat < Word.size := a'.start.isLt
    replace hdisj : ∀ a ∈ live, a.range.Disjoint ⟨a'.start.toNat, size⟩ := by
      simpa [Allocation.range, hsize] using hdisj
    replace hfit : a'.start.toNat + size ≤ Word.size := by simpa [Allocation.end, hsize] using hfit
    generalize a'.start.toNat = t at hlt hdisj hfit
    induction t with
    | zero => exact ⟨0, .head _, hlt, hfit, hdisj⟩
    | succ t ih =>
      by_cases he : ∃ a ∈ live, a.end = t + 1
      · exact ⟨t + 1, .tail _ (List.mem_map.2 he), hlt, hfit, hdisj⟩
      · refine ih (by omega) (fun a ha => ?_) (by omega)
        have := hdisj a ha
        have : a.end ≠ t + 1 := fun h => he ⟨a, ha, h⟩
        simp only [NatRange.Disjoint, NatRange.end, Allocation.range, Allocation.end,
          Allocation.size] at *
        omega

inductive MemoryBranchOp
  | alloc (size : Word) (live : List Allocation) (ha : ∃ a', ValidAlloc live size.toNat a')

abbrev MemoryND : NonDeterminism where
  Op := MemoryBranchOp
  Resp
    | .alloc size live _ha => { a' : Allocation // ValidAlloc live size.toNat a' }
  resp_nonempty
    | .alloc _ _ ha => let ⟨a, h⟩ := ha; ⟨a, h⟩

abbrev MemState := Array Allocation

def MemState.live : MemState → Array Allocation := id
def MemState.push : MemState → Allocation → MemState := Array.push

namespace MemState

/-- Evidence that one allocation of `m` holds all of `[offset, offset + length)`. -/
abbrev Region (m : MemState) (offset : Word) (length : Nat) :=
  { j : Fin m.size // m[j].start.toNat ≤ offset.toNat ∧ offset.toNat + length ≤ m[j].end }

def inBounds (m : MemState) (offset : Word) (length : Nat) : Option (m.Region offset length) :=
  (List.finRange m.size).findSome? fun j =>
    if h : m[j].start.toNat ≤ offset.toNat ∧ offset.toNat + length ≤ m[j].end then some ⟨j, h⟩
    else none

def read (m : MemState) {offset : Word} {length : Nat} (r : m.Region offset length) : ByteArray :=
  let start := (offset - m[r.1].start).toNat
  m[r.1].bytes.extract start (start + length)

def write (m : MemState) {offset : Word} {length : Nat} (bytes : ByteArray)
    (r : m.Region offset length) : MemState :=
  m.modify r.1 fun a => { a with bytes := bytes.copySlice 0 a.bytes (offset - a.start).toNat length }

end MemState

def memStep {X : Type} (mem : MemState) : Step EvalE .none Empty X → Step HostE MemoryND UB (MemState × X)
  | .silent x => .silent (mem, x)
  | .impure (.inl hostOp) k => .impure hostOp fun r => (mem, k r)
  | .impure (.inr sirOp) k => match sirOp with
    | .ub ub => .pure ub
    | .alloc kind size =>
      if h : ∃ a', ValidAlloc mem.live.toList size.toNat a'
      then .branch (.alloc size mem.live.toList h) fun ⟨a', _⟩ =>
        let a' := match kind with
          | .zeroed => { a' with bytes := ⟨.replicate a'.size 0⟩ }
          | .uninitialized => a'
        let mem' := if size > 0 then mem.push a' else mem
        (mem', k a'.start)
      else .pure (.outOfMemory size)
    | .read offset len =>
      if len = 0 then .silent (mem, k .empty) else
      match mem.inBounds offset len.toNat with
      | some r => .silent (mem, k (mem.read r))
      | none => .pure (.memoryOutOfBounds offset len.toNat)
    | .write offset bytes =>
      if bytes.size = 0 then .silent (mem, k ()) else
      match mem.inBounds offset bytes.size with
      | some r => .silent (mem.write bytes r, k ())
      | none => .pure (.memoryOutOfBounds offset bytes.size)
    | .copy ⟨dst, src, len⟩ =>
      if len = 0 then .silent (mem, k ()) else
      match mem.inBounds src len.toNat, mem.inBounds dst len.toNat with
      | some r, some w => .silent (mem.write (mem.read r) w, k ())
      | none, _ => .pure (.memoryOutOfBounds src len.toNat)
      | _, none => .pure (.memoryOutOfBounds dst len.toNat)
  | .pure a => nomatch a
  | .branch c _ => nomatch c

def interpMem (sir : SirM Empty) : CoFree HostE MemoryND UB := CoFree.interp memStep #[] sir

end Sir
