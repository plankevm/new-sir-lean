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

/-- Evidence that `[offset, offset + length)` may be accessed: it is empty, or one allocation of
`m` holds all of it. -/
inductive Region (m : MemState) (offset length : Nat) : Type
  | empty : length = 0 → Region m offset length
  | within (j : Fin m.size) : m[j].start.toNat ≤ offset ∧ offset + length ≤ m[j].end →
      Region m offset length

def inBounds (m : MemState) (offset length : Nat) : Option (m.Region offset length) :=
  if h : length = 0 then some (.empty h) else
  (List.finRange m.size).findSome? fun j =>
    if h : m[j].start.toNat ≤ offset ∧ offset + length ≤ m[j].end then some (.within j h) else none

def read (m : MemState) {offset length : Nat} : m.Region offset length → ByteArray
  | .empty _ => .empty
  | .within j _ =>
    let start := offset - m[j].start.toNat
    m[j].bytes.extract start (start + length)

def write (m : MemState) {offset length : Nat} (bytes : ByteArray) :
    m.Region offset length → MemState
  | .empty _ => m
  | .within j _ =>
    m.modify j fun a =>
      { a with bytes := bytes.copySlice 0 a.bytes (offset - a.start.toNat) length }

end MemState

def interpMem (sir : SirM Empty) : CoFree HostE MemoryND UB where
  State := MemState × sir.Pos
  Jump := PEmpty
  initial := (#[], sir.initPos)
  step := fun (mem, pos) => match sir.stepAt pos with
    | .pure a => nomatch a
    | .silent pos' => .silent <| .inl (mem, pos')
    | .impure (.inl hostOp) k => .impure hostOp fun r => .inl (mem, k r)
    | .impure (.inr sirOp) k => match sirOp with
      | .ub ub => .pure ub
      | .alloc kind size =>
        if h : ∃ a', ValidAlloc mem.live.toList size.toNat a'
        then .branch (.alloc size mem.live.toList h) fun ⟨a', _⟩ =>
          let a' := match kind with
            | .zeroed => { a' with bytes := ⟨.replicate a'.size 0⟩ }
            | .uninitialized => a'
          .inl (mem.push a', k a'.start)
        else .pure (.outOfMemory size)
      | .read offset len => match mem.inBounds offset.toNat len.toNat with
        | some r => .silent <| .inl (mem, k (mem.read r))
        | none => .pure (.memoryOutOfBounds offset.toNat len.toNat)
      | .write offset bytes => match mem.inBounds offset.toNat bytes.size with
        | some r => .silent <| .inl (mem.write bytes r, k ())
        | none => .pure (.memoryOutOfBounds offset.toNat bytes.size)
      | .copy ⟨dst, src, len⟩ =>
        match mem.inBounds src.toNat len.toNat, mem.inBounds dst.toNat len.toNat with
        | some r, some w => .silent <| .inl (mem.write (mem.read r) w, k ())
        | none, _ => .pure (.memoryOutOfBounds src.toNat len.toNat)
        | _, none => .pure (.memoryOutOfBounds dst.toNat len.toNat)
    | .branch c _ => nomatch c
  target := nofun

end Sir
