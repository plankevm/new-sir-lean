import Sir.Eval

/-! Frame memory: a list of allocations, plus the return data buffer. A new allocation is placed
by a branch (`Choice.placement`) over every valid placement. A byte is `none` until written if it came from `mallocany`.
Reading a byte outside every allocation, reading a `none` byte, writing outside every
allocation, and allocating when no placement exists are undefined behavior (`fault`). `mcopy`
moves byte states, so copying unwritten bytes is not itself a read. -/

namespace Sir

open CoFree (perform)

structure Allocation where
  start : Nat
  bytes : Array (Option UInt8)

def Allocation.contains (a : Allocation) (addr : Nat) : Bool :=
  a.start ≤ addr && addr < a.start + a.bytes.size

def Allocation.write (a : Allocation) (offset : Nat) (bytes : Array (Option UInt8)) : Allocation :=
  { a with bytes := (List.range bytes.size).foldl (init := a.bytes) fun acc i =>
      if a.contains (offset + i) then acc.set! (offset + i - a.start) bytes[i]! else acc }

structure FrameMem where
  allocs : Array Allocation := #[]
  returnData : ByteArray := .empty

namespace FrameMem

/-- `none` outside every allocation; `some none` for an unwritten byte of a `mallocany`. -/
def byte? (m : FrameMem) (addr : Nat) : Option (Option UInt8) :=
  m.allocs.findSome? fun a => if a.contains addr then some a.bytes[addr - a.start]! else none

/-- The states of `length` bytes from `offset`, or `none` if any lies outside every allocation. -/
def states? (m : FrameMem) (offset length : Nat) : Option (Array (Option UInt8)) :=
  (Array.range length).mapM fun i => m.byte? (offset + i)

def write (m : FrameMem) (offset : Nat) (bytes : Array (Option UInt8)) : FrameMem :=
  { m with allocs := m.allocs.map (·.write offset bytes) }

def live (m : FrameMem) : List (Nat × Nat) :=
  m.allocs.toList.filterMap fun a => if a.bytes.size = 0 then none else some (a.start, a.bytes.size)

end FrameMem

/-- The lowest placement starts at 0 or right after a live allocation, so if none of these
candidates fits, no placement exists. -/
def placeable (live : List (Nat × Nat)) (size : Nat) : Bool :=
  (0 :: live.map fun a => a.1 + a.2).any fun s => decide (Placement live size s)

theorem exists_placement_of_placeable {live : List (Nat × Nat)} {size : Nat}
    (h : placeable live size = true) : ∃ start, Placement live size start := by
  simp only [placeable, List.any_eq_true, decide_eq_true_eq] at h
  exact let ⟨start, _, h⟩ := h; ⟨start, h⟩

def ub {α : Type} (u : UB) : CoFree Exec α := do
  let e ← perform (E := Exec) (.fault (.ub u))
  Empty.elim e

def handleMem : FrameMem → (op : SirE.Op) → CoFree Exec (FrameMem × SirE.Resp op)
  | m, .inr op => do
    let r ← perform (E := Exec) op
    pure (m, r)
  | m, .inl (.alloc zeroed size) =>
    if fits : placeable m.live size then do
      let ⟨start, _⟩ ← CoFree.choose (E := Exec)
        (.placement size m.live (exists_placement_of_placeable fits))
      let a : Allocation := ⟨start, .replicate size (if zeroed then some 0 else none)⟩
      pure ({ m with allocs := m.allocs.push a }, BitVec.ofNat 256 start)
    else ub (.outOfMemory size)
  | m, .inl (.read offset length) => do
    let some states := m.states? offset length | ub (.memoryOutOfBounds offset length)
    let some bs := states.mapM id | ub (.uninitializedRead offset length)
    pure (m, ⟨bs⟩)
  | m, .inl (.write offset bytes) => do
    unless (m.states? offset bytes.size).isSome do ub (.memoryOutOfBounds offset bytes.size)
    pure (m.write offset (bytes.data.map some), ())
  | m, .inl (.copy dst src length) => do
    let some bs := m.states? src length | ub (.memoryOutOfBounds src length)
    unless (m.states? dst length).isSome do ub (.memoryOutOfBounds dst length)
    pure (m.write dst bs, ())
  | m, .inl .returnData => pure (m, m.returnData)
  | m, .inl (.setReturnData bytes) => pure ({ m with returnData := bytes }, ())

/-- The semantics of an entry point: host interactions and placement choices. -/
def exec (p : Program) (layout : Layout) (imm : Immutables p) (env : Env) (e : Entry) :
    CoFree Exec Empty := do
  let (_frame', res) ←
    CoFree.interpState handleMem (.sum (.empty nofun) (.empty nofun)) {} (runEntry p layout imm env e)
  nomatch res

end Sir
