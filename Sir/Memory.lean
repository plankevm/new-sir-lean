import Sir.Eval

/-! Frame memory: a list of allocations, plus the return data buffer. Placement of new
allocations is chosen by the host. Bytes never written to an allocation from `mallocany`, and
bytes outside every allocation, read as an arbitrary byte (`anyByte`) on each read; writing
outside every allocation is undefined behavior. -/

namespace Sir

open CoFree (perform)

structure Allocation where
  start : Nat
  bytes : Array (Option UInt8)

def Allocation.contains (a : Allocation) (addr : Nat) : Bool :=
  a.start ≤ addr && addr < a.start + a.bytes.size

def Allocation.write (a : Allocation) (offset : Nat) (bytes : ByteArray) : Allocation :=
  { a with bytes := (List.range bytes.size).foldl (init := a.bytes) fun acc i =>
      if a.contains (offset + i) then acc.set! (offset + i - a.start) (some bytes[i]!) else acc }

structure FrameMem where
  allocs : Array Allocation := #[]
  returnData : ByteArray := .empty

namespace FrameMem

/-- `none` outside every allocation; `some none` for an unwritten byte of a `mallocany`. -/
def byte? (m : FrameMem) (addr : Nat) : Option (Option UInt8) :=
  m.allocs.findSome? fun a => if a.contains addr then some a.bytes[addr - a.start]! else none

def allocated (m : FrameMem) (offset length : Nat) : Bool :=
  (List.range length).all fun i => (m.byte? (offset + i)).isSome

def live (m : FrameMem) : List (Nat × Nat) :=
  m.allocs.toList.filterMap fun a => if a.bytes.size = 0 then none else some (a.start, a.bytes.size)

end FrameMem

def handleMem : FrameMem → (op : SirE.Op) → CoFree Host (FrameMem × SirE.Resp op)
  | m, .inr op => (perform (E := Host) op).bind fun r => pure (m, r)
  | m, .inl (.alloc zeroed size) => do
    let ⟨start, _⟩ ← perform (E := Host) (.alloc size m.live)
    let a : Allocation := ⟨start, .replicate size (if zeroed then some 0 else none)⟩
    pure ({ m with allocs := m.allocs.push a }, BitVec.ofNat 256 start)
  | m, .inl (.read offset length) => do
    let mut out := ByteArray.empty
    for i in List.range length do
      match m.byte? (offset + i) with
      | some (some b) => out := out.push b
      | _ => out := out.push (← perform (E := Host) .anyByte)
    pure (m, out)
  | m, .inl (.write offset bytes) =>
    if m.allocated offset bytes.size then
      pure ({ m with allocs := m.allocs.map (·.write offset bytes) }, ())
    else do
      let e ← perform (E := Host) (.fault (.memoryOutOfBounds offset bytes.size))
      Empty.elim e
  | m, .inl .returnData => pure (m, m.returnData)
  | m, .inl (.setReturnData bytes) => pure ({ m with returnData := bytes }, ())

/-- The semantics of an entry point: every remaining effect is a host interaction. -/
def exec (p : Program) (layout : Layout) (e : Entry) : CoFree Host Empty :=
  (CoFree.interpState handleMem {} (runEntry p layout e)).bind fun r => Empty.elim r.2

end Sir
