import Sir.Effect

open Host
open CoFree (perform branch)

namespace Sir

structure Allocation where
  start : Word
  bytes : ByteArray

def Allocation.size (a : Allocation) : Nat := a.bytes.size
def Allocation.range (a : Allocation) : NatRange := ⟨a.start.toNat, a.size⟩
def Allocation.end (a : Allocation) : Nat := a.start.toNat + a.size

def Allocation.contains (a : Allocation) (addr : Nat) : Prop := addr ∈ a.range

structure MemState where
  reserved : NatRange
  cumAlloced : UInt64 := 0
  live : Array Allocation := #[]

namespace MemState

def push (s : MemState) (a' :  Allocation) : MemState :=
  { s with live := s.live.push a', cumAlloced := s.cumAlloced + .ofNat a'.size }
def allocCount (s : MemState) : Nat := s.live.size
def taken (s : MemState) : List NatRange := s.reserved :: s.live.toList.map Allocation.range

/-- Evidence that one allocation of `m` holds all of `[offset, offset + length)`. -/
abbrev Region (m : MemState) (offset : Word) (length : Nat) :=
  { j : Fin m.live.size // m.live[j].start.toNat ≤ offset.toNat ∧ offset.toNat + length ≤ m.live[j].end }

def inBounds (m : MemState) (offset : Word) (length : Nat) : Option (m.Region offset length) :=
  (List.finRange m.allocCount).findSome? fun j =>
    if h : m.live[j].start.toNat ≤ offset.toNat ∧ offset.toNat + length ≤ m.live[j].end then some ⟨j, h⟩
    else none

def read (m : MemState) {offset : Word} {length : Nat} (r : m.Region offset length) : ByteArray :=
  let start := (offset - m.live[r.val].start).toNat
  m.live[r.val].bytes.extract start (start + length)

def write (m : MemState) {offset : Word} {length : Nat} (bytes : ByteArray) (r : m.Region offset length) : MemState :=
  { m with live := m.live.modify r.val fun a => { a with bytes := bytes.copySlice 0 a.bytes (offset - a.start).toNat length } }

def ValidAlloc (m : MemState) (size : Nat) (a' : Allocation) : Prop :=
  a'.size = size ∧ a'.end ≤ Word.size ∧ (0 < size → ∀ r ∈ m.taken, r.Disjoint a'.range)

instance (m : MemState) (size : Nat) : DecidablePred (m.ValidAlloc size) := by
  unfold ValidAlloc; infer_instance

private def zeroedAt (size start : Nat) : Allocation := ⟨Word.ofNat start, ⟨.replicate size 0⟩⟩

instance (m : MemState) (size : Nat) : Decidable (∃ a', m.ValidAlloc size a') :=
  decidable_of_iff (∃ s ∈ (0 : Nat) :: m.taken.map NatRange.end, s < Word.size ∧
      s + size ≤ Word.size ∧ (0 < size → ∀ r ∈ m.taken, r.Disjoint ⟨s, size⟩)) <| by
    have valid {t} (ht : t < Word.size) : m.ValidAlloc size (zeroedAt size t) ↔
        t + size ≤ Word.size ∧ (0 < size → ∀ r ∈ m.taken, r.Disjoint ⟨t, size⟩) := by
      have : (Word.ofNat t).toNat = t := Nat.mod_eq_of_lt ht
      have hsz : (⟨.replicate size 0⟩ : ByteArray).size = size := by simp [ByteArray.size]
      simp [ValidAlloc, Allocation.range, Allocation.end, Allocation.size, zeroedAt, hsz, this]
    refine ⟨fun ⟨_, _, ht, h⟩ => ⟨_, (valid ht).2 h⟩, fun ⟨a', hsize, hfit, hdisj⟩ => ?_⟩
    have hlt : a'.start.toNat < Word.size := a'.start.isLt
    replace hfit : a'.start.toNat + size ≤ Word.size := by simpa [Allocation.end, hsize] using hfit
    rcases Nat.eq_zero_or_pos size with hz | hpos
    · exact ⟨0, .head _, by decide, by omega, by omega⟩
    replace hdisj : ∀ r ∈ m.taken, r.Disjoint ⟨a'.start.toNat, size⟩ := by
      simpa [Allocation.range, hsize] using hdisj hpos
    generalize a'.start.toNat = t at hlt hdisj hfit
    induction t with
    | zero => exact ⟨0, .head _, hlt, hfit, fun _ => hdisj⟩
    | succ t ih =>
      by_cases he : ∃ r ∈ m.taken, r.end = t + 1
      · exact ⟨t + 1, .tail _ (List.mem_map.2 he), hlt, hfit, fun _ => hdisj⟩
      · refine ih (by omega) (fun r hr => ?_) (by omega)
        have := hdisj r hr
        have : r.end ≠ t + 1 := fun h => he ⟨r, hr, h⟩
        simp only [NatRange.Disjoint, NatRange.end] at *
        omega

end MemState

inductive MemoryBranchOp
  | pick (n : Nat) (h : 0 < n)
  | alloc (size : Word) (mem : MemState) (ha : ∃ a', mem.ValidAlloc size.toNat a')

abbrev MemoryND : NonDeterminism where
  Op := MemoryBranchOp
  Resp
    | .pick n _ => Fin n
    | .alloc size mem _ha => { a' : Allocation // mem.ValidAlloc size.toNat a' }
  resp_nonempty
    | .pick _ h => ⟨0, h⟩
    | .alloc _ _ ha => let ⟨a, h⟩ := ha; ⟨a, h⟩

def memStep {X : Type} (mem : MemState) : Step EvalE .none Empty X → Step HostE MemoryND UB (MemState × X)
  | .silent x => .silent (mem, x)
  | .impure (.inl hostOp) k => .impure hostOp fun r => (mem, k r)
  | .impure (.inr sirOp) k => match sirOp with
    | .ub ub => .pure ub
    | .alloc kind size =>
      if mem.cumAlloced.toNat + size.toNat ≥ UInt64.size
      then .pure (.outOfMemory size)
      else if h : ∃ a', mem.ValidAlloc size.toNat a' then
        .branch (.alloc size mem h) fun ⟨a', _⟩ =>
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


def CompilerReservedBytes : Nat := 2^32

def interpMem (sir : SirM Empty) : CoFree HostE MemoryND UB := do
  let start ← branch (N := MemoryND) (.pick (Word.size - CompilerReservedBytes) (by decide))
  CoFree.interp memStep { reserved := ⟨start.val, CompilerReservedBytes⟩ } sir

end Sir
