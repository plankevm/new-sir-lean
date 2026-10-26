import Sir.Eval

/-! Frame memory: a list of allocations, plus the return data buffer. A new allocation is placed
by a branch (`Choice.placement`) over every valid placement. A byte is `none` until written if it came from `mallocany`.
Reading a byte outside every allocation, reading a `none` byte, writing outside every
allocation, and allocating when no placement exists are undefined behavior (`fault`). `mcopy`
moves byte states, so copying unwritten bytes is not itself a read. -/

namespace Sir

open Host

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

def live (m : FrameMem) : List MemRange :=
  (m.allocs.toList.filter (·.bytes.size > 0)).map (fun a => ⟨a.start, a.bytes.size⟩)

end FrameMem

def ub {α : Type} (u : UB) : CoFree (HostE Fault) α := do
  let e ← perform (E := HostE Fault) (.fault (.ub u))
  Empty.elim e

def handleMem : FrameMem → (op : SirE.Op) → CoFree (HostE Fault) (FrameMem × SirE.Resp op)
  | m, .inr op => do
    let r ← perform (E := HostE Fault) op
    pure (m, r)
  | m, .inl (.alloc zeroed size) =>
    if fits : ∃ start, MemRange.Placement ⟨start, size⟩ m.live then do
      let ⟨start, _⟩ ← CoFree.choose (E := HostE Fault) (.placement size m.live fits)
      let a : Allocation := ⟨start, .replicate size (if zeroed then some 0 else none)⟩
      pure ({ m with allocs := m.allocs.push a }, Word.ofNat start)
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

/-- The semantics of an entry point with storage and the world left abstract. -/
def execHost (p : Program) (layout : Layout) (imm : Immutables p) (env : Env) (e : Entry) :
    CoFree (HostE Fault) Empty := do
  let (_, res) ← CoFree.interpState handleMem (.sum (.empty nofun) .id) {} (runEntry p layout imm env e)
  nomatch res

/-- The semantics of an entry point started in state `s`: world interactions and placement
choices. -/
def exec (p : Program) (layout : Layout) (imm : Immutables p) (env : Env) (e : Entry) (s : State) :
    CoFree Exec Empty := do
  let (_, res) ← Host.interpStore env s (execHost p layout imm env e)
  nomatch res

end Sir
