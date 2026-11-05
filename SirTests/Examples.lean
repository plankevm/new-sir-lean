import SirTests.Host
import Sir.Syntax

namespace SirTests.Examples

open Sir Host

def b8 : ByteSize := ⟨1, by decide⟩
def b16 : ByteSize := ⟨2, by decide⟩
def b32bit : ByteSize := ⟨4, by decide⟩
def b32 : ByteSize := ⟨32, by decide⟩

def zeroSlot (n : Nat) (s : ByteSize) (off : UInt32) (h : off.toNat + s.toNat ≤ n) :
    MappingOffset ⟨.replicate n 0⟩ (zeros s) :=
  ⟨off, fun i hi => by
    have hz : (zeros s).size = s.toNat := Array.size_replicate
    have hlt : off.toNat + i < (⟨.replicate n 0⟩ : ByteArray).size := by
      show _ < (Array.replicate n 0).size
      rw [Array.size_replicate]; omega
    rw [getElem?_pos (⟨.replicate n 0⟩ : ByteArray) (off.toNat + i) hlt, ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data]
    simp [zeros]⟩

def selfOffset (b : ByteArray) : MappingOffset b b :=
  ⟨0, fun i h => by simp only [UInt32.toNat_zero, Nat.zero_add]; exact getElem?_pos b i h⟩

def initOnly (blocks : Array Block) (extra : Array Function := #[]) : Program where
  init := 0
  main := 0
  functions := #[⟨0, .never, blocks⟩] ++ extra
  mainDatas := []

/-- `for i in 0..10: acc += i`, then `sstore 0 acc`. -/
def loopSum : Program := sir! {
  fn init:
    entry -> i0 acc0 {
      i0 = const 0
      acc0 = const 0
      => @head
    }
    head i acc -> i2 acc2 {
      acc2 = add acc i
      i2 = add i 1
      c = lt i2 10
      => c ? @head : @done
    }
    done n total {
      sstore 0 total
      stop
    }
  fn main:
    entry { stop }
}

/-- An internal call returning two values, whose results are returned as ABI words. -/
def internalCall : Program := sir! {
  fn init:
    entry {
      x y = icall @pair 3 4
      n = const 64
      p = malloc n
      mstore256 p x
      q = add p 32
      mstore256 q y
      return p n
    }
  fn pair -> 2:
    entry a b -> s m {
      s = add a b
      m = mul a b
      iret
    }
  fn main:
    entry { stop }
}

def memory : Program := sir! {
  fn init:
    entry {
      n = const 32
      p = malloc n
      mstore256 p ((0xAB : Word) <<< 248)
      a = mload8 p
      p1 = add p 1
      mstore16 p1 0xBEEF
      b = mload256 p
      h = keccak256 p n
      four = const 4
      q = mallocany n
      mcopy q p four
      c = mload32 q
      sstore 0 a
      sstore 1 b
      sstore 2 h
      sstore 3 c
      log2 p four 0 1
      stop
    }
  fn main:
    entry { stop }
}

def oobWrite : Program := sir! {
  fn init:
    entry {
      mstore8 0x10 0
      stop
    }
  fn main:
    entry { stop }
}

def oobRead : Program := sir! {
  fn init:
    entry {
      n = const 4
      p = malloc n
      x = mload256 p
      stop
    }
  fn main:
    entry { stop }
}

def outOfMemory : Program := sir! {
  fn init:
    entry {
      p = malloc 32
      q = malloc (BitVec.allOnes 256)
      stop
    }
  fn main:
    entry { stop }
}

def revert : Program := sir! {
  fn init:
    entry {
      n = const 2
      p = malloc n
      mstore16 p 0xDEAD
      revert p n
    }
  fn main:
    entry { stop }
}

def spin : Program := sir! {
  fn init:
    entry { => @entry }
  fn main:
    entry { stop }
}

def spinLogging : Program := sir! {
  fn init:
    entry {
      z = const 0
      log0 z z
      => @entry
    }
  fn main:
    entry { stop }
}

def spinInCallee : Program := sir! {
  fn init:
    entry {
      icall @spin
      stop
    }
  fn spin -> 0:
    entry { => @entry }
  fn main:
    entry { stop }
}

/-- `init` patches immutable 0 (2 bytes) into an 8-byte runtime copy; `main` reads it. -/
def immutables : Program := sir! {
  immutable value 2
  fn init:
    entry {
      len = runtime_length
      p = malloc len
      setimmutable %value p 0xABCD
      return p len
    }
  fn main:
    entry {
      a = getimmutable %value
      sstore 0 a
      b = getimmutable %value
      sstore 1 b
      stop
    }
}

theorem imm_fits (o : Nat) (ho : o ≤ 6) :
    ∀ i : Fin immutables.immutables.size, o + immutables.immutables[i].toNat ≤ 8
  | ⟨0, _⟩ => Nat.add_le_add_right ho 2

def immLayout : Layout immutables where
  init := ⟨.replicate 8 0⟩
  init_u32 := by decide
  main := ⟨.replicate 8 0⟩
  main_u32 := by decide
  mainStartOffset := selfOffset _
  initDataOffsets i := absurd i.isLt (Nat.not_lt_zero _)
  mainDataOffsets i := absurd i.isLt (Nat.not_lt_zero _)
  immutableOffsets i := [zeroSlot 8 _ 1 (imm_fits 1 (by decide) i), zeroSlot 8 _ 5 (imm_fits 5 (by decide) i)]
  atLeastOne_immOffsets _ := Nat.zero_lt_succ _
  no_imm_imm_overlap := by
    intro ⟨i, hi⟩ ⟨i', hi'⟩ ⟨mo, hmo⟩ ⟨mo', hmo'⟩
    obtain rfl : i = 0 := by simp [immutables] at hi; omega
    obtain rfl : i' = 0 := by simp [immutables] at hi'; omega
    simp only [List.length_cons, List.length_nil] at hmo hmo'
    match mo, mo', hmo, hmo' with
    | 0, 0, _, _ => exact .inl ⟨rfl, .rfl⟩
    | 1, 1, _, _ => exact .inl ⟨rfl, .rfl⟩
    | 0, 1, _, _ => exact .inr (by decide +revert)
    | 1, 0, _, _ => exact .inr (by decide +revert)
  no_imm_data_overlap d := absurd d.isLt (Nat.not_lt_zero _)

def callsThen (tail : Array (Operation VarId)) : Program := initOnly #[
  { ops := #[.let 1 (.const 4), .let 2 (.malloc 1), .let 10 (.const 100), .let 11 (.const 0xBEEF),
      .let 12 (.const 0), .let 13 (.const 2), .let 3 (.call 10 11 12 2 12 2 13),
      .let 4 .returndatasize, .let 5 (.mload b16 2), .let 21 (.const 1), .let 22 (.const 2),
      .stmt (.sstore 12 3), .stmt (.sstore 21 4), .stmt (.sstore 22 5)] ++ tail,
    control := .stop }]

/-- Allocates 4 bytes at `ptr` (var 2), sets var 14 := `ptr + 3`, var 15 := 2, then runs `ops`. -/
def withBuffer (ops : Array (Operation VarId)) : Program := initOnly #[
  { ops := #[.let 1 (.const 4), .let 2 (.malloc 1), .let 10 (.const 100), .let 11 (.const 0xBEEF),
      .let 12 (.const 0), .let 13 (.const 3), .let 14 (.binop .add 2 13),
      .let 15 (.const 2)] ++ ops,
    control := .stop }]

def callOutputPastAlloc : Program := withBuffer #[.let 3 (.call 10 11 12 2 12 14 15)]

def callShortOutput : Program :=
  withBuffer #[.let 16 (.const 64), .let 3 (.call 10 11 12 2 12 2 16)]

def returnDataCopyPastAlloc : Program :=
  withBuffer #[.let 3 (.call 10 11 12 2 12 2 12), .stmt (.returndatacopy 14 12 15)]

def returnDataCopyPastBoth : Program :=
  withBuffer #[.let 3 (.call 10 11 12 2 12 2 12), .stmt (.returndatacopy 14 15 15)]

def switchOn (v : Word) : Program := sir! {
  fn init:
    entry {
      x = const (v)
      switch x { 1 => @one 7 => @seven }
    }
    one {
      sstore 1 1
      stop
    }
    seven {
      sstore 2 2
      stop
    }
  fn main:
    entry { stop }
}

def environment : Program := sir! {
  data nine 0x09
  fn init:
    entry { stop }
  fn main:
    entry {
      one = const 1
      cd = calldataload one
      sz = calldatasize
      d = data_offset .nine
      z = const 0
      c = create2 z z z one
      who = caller
      sstore z cd
      sstore 1 sz
      sstore 2 d
      sstore 3 c
      sstore 4 who
      selfdestruct who
    }
}

def envLayout : Layout environment where
  init := ⟨#[9]⟩
  init_u32 := by decide
  main := ⟨#[9]⟩
  main_u32 := by decide
  mainStartOffset := selfOffset _
  initDataOffsets | ⟨0, _⟩ => selfOffset _
  mainDataOffsets | ⟨0, _⟩, _ => selfOffset _
  immutableOffsets i := absurd i.isLt (Nat.not_lt_zero _)
  atLeastOne_immOffsets i := absurd i.isLt (Nat.not_lt_zero _)
  no_imm_imm_overlap i := absurd i.isLt (Nat.not_lt_zero _)
  no_imm_data_overlap _ im := absurd im.isLt (Nat.not_lt_zero _)

def undefinedVar : Program := sir! {
  fn init:
    entry {
      sstore $1 $2
      stop
    }
  fn main:
    entry { stop }
}

/-- `sub`, `shl` and `addmod` take their first input as the EVM top of stack. -/
def pureOps : Program := sir! {
  fn init:
    entry {
      a = const 10
      b = const 3
      z = const 0
      f = const 4
      s = sub a b
      l = shl b a
      m = addmod a b f
      i = iszero z
      sstore z s
      sstore b l
      sstore f m
      sstore i i
      stop
    }
  fn main:
    entry { stop }
}

/-- Block ids are local: function 0 has one block, so block 1 is out of range even though
function 1 has a block 1. -/
def foreignBlock : Program := sir! {
  fn init:
    entry { => @1 }
  fn other:
    entry { stop }
    second { stop }
  fn main:
    entry { stop }
}

def neverCalleeHalts : Program := sir! {
  fn init:
    entry { icall_never @callee }
  fn callee:
    entry { stop }
  fn main:
    entry { stop }
}

def neverCalleeReturns : Program := sir! {
  fn init:
    entry { icall_never @callee }
  fn callee -> 0:
    entry { iret }
  fn main:
    entry { stop }
}

def entryReturns : Program := sir! {
  fn init:
    entry { iret }
  fn main:
    entry { stop }
}

def entryReturnsValues : Program := sir! {
  fn init -> 0:
    entry { iret }
  fn main:
    entry { stop }
}

def runOut (p : Program) (l : Layout p := by exact plainLayout _) : Run :=
  runInit p l (world := { callResult := (true, ⟨#[1, 2, 3]⟩) })

def wordBytes (n : Nat) : List UInt8 := (Word.toBytes b32 (BitVec.ofNat 256 n)).toList

def immValues : MainImmutables := ⟨#[0x2345], .empty⟩

def checks : List (String × Bool) :=
  let mem := runInit memory
  let call := runOut (callsThen #[])
  let spun := runInit spinLogging (fuel := 1000)
  let env := runMain environment noImmutables envLayout (calldata := ⟨#[1, 2, 3]⟩)
  [ ("loop sums 0..9", (runInit loopSum).result == .ret [] && (runInit loopSum).slot 0 == 45),
    ("pure ops in stack order", (runInit pureOps).result == .ret [] &&
      (runInit pureOps).slots [0, 3, 4, 1] == [7, 80, 1, 1]),
    ("icall returns (7, 12)", (runInit internalCall).result == .ret (wordBytes 7 ++ wordBytes 12)),
    ("UB: out-of-allocation write", (runInit oobWrite).result == .ub (.memoryOutOfBounds 0x10 1)),
    ("memory: mload8, partial mstore16, keccak, mcopy into mallocany",
      mem.result == .ret [] && mem.slots [0, 1, 2, 3] == ([0xAB, (0xABBEEF : Word) <<< 232,
       0x3e889ef1ce94d5e823a41b0e65c5e971dcd08e9d92a3dff1038a5eeefc54f39d, 0xABBEEF00] : List Word)),
    ("UB: out-of-allocation read", (runInit oobRead).result == .ub (.memoryOutOfBounds 0x80 32)),
    ("UB: no placement for an allocation",
      (runInit outOfMemory).result == .ub (.outOfMemory (BitVec.allOnes 256))),
    ("memory: log2", mem.world.logs.toList == [([0, 1], [0xAB, 0xBE, 0xEF, 0])]),
    ("revert with data", (runInit revert).result == .revert [0xDE, 0xAD]),
    ("divergence: out of fuel", (runInit spin (fuel := 1000)).result == .outOfFuel),
    ("divergence: effects before it are observed",
      spun.result == .outOfFuel && spun.world.logs.size > 10),
    ("divergence inside a callee", (runInit spinInCallee (fuel := 1000)).result == .outOfFuel),
    ("setimmutable patches every placeholder",
      (runInit immutables immLayout).result == .ret [0, 0xAB, 0xCD, 0, 0, 0xAB, 0xCD, 0]),
    ("getimmutable: the run's fixed value, the same on every read, without world operations",
      let r := runMain immutables immValues immLayout
      r.result == .ret [] && r.slots [0, 1] == [0x2345, 0x2345] && r.world.ops == 0),
    ("call: success, returndatasize, truncated return copy",
      call.result == .ret [] && call.slots [0, 1, 2] == [1, 3, 0x0102]),
    ("call: request", call.world.calls.toList == [(.call 0, 0xBEEF, [])]),
    ("returndatacopy out of bounds is invalid",
      (runOut (callsThen #[.stmt (.returndatacopy 2 13 13)])).result == .invalid),
    ("UB: call output written past the allocation",
      (runOut callOutputPastAlloc).result == .ub (.memoryOutOfBounds 0x83 2)),
    ("call writes only the bytes returned, not the whole requested range",
      (runOut callShortOutput).result == .ret []),
    ("UB: returndatacopy destination past the allocation",
      (runOut returnDataCopyPastAlloc).result == .ub (.memoryOutOfBounds 0x83 2)),
    ("returndatacopy source past the return data is invalid even if the destination is too",
      (runOut returnDataCopyPastBoth).result == .invalid),
    ("switch takes the matching case", (runInit (switchOn 7)).slots [1, 2] == [0, 2]),
    ("UB: switch without match or fallback", (runInit (switchOn 9)).result == .ub .switchNoMatch),
    ("environment", env.result == .selfdestruct 0xC0 && env.slots [0, 1, 2, 3, 4] ==
      ([(0x0203 : Word) <<< 240, 3, 0, 0xC2, 0xC0] : List Word)),
    ("UB: undefined variable", (runInit undefinedVar).result == .malformed),
    ("UB: blocks are local to their function", (runInit foreignBlock).result == .malformed),
    ("icall_never: the callee halts", (runInit neverCalleeHalts).result == .ret []),
    ("UB: icall_never callee returning",
      (runInit neverCalleeReturns).result == .malformed),
    ("UB: returning from an entry",
      (runInit entryReturns).result == .malformed),
    ("UB: an entry function declared to return values returning",
      (runInit entryReturnsValues).result == .malformed) ]

/-! Concrete storage. -/
/-- `sstore 0 5`, then `c`, then `sstore 1 (sload 0)`, `sstore 2 (balance 0xB)`. -/
def storeAround (c : Expr VarId) (ops : Array (Operation VarId) := #[]) : Program := initOnly #[
  { ops := #[.let 1 (.const 0), .let 2 (.const 5), .stmt (.sstore 1 2), .let 10 (.const 0)] ++ ops ++
      #[.let 3 c, .let 4 (.sload 1), .let 5 (.const 1), .stmt (.sstore 5 4), .let 6 (.const 0xB),
        .let 7 (.balance 6), .let 8 (.const 2), .stmt (.sstore 8 7)],
    control := .stop }]

def transient : Program := initOnly #[
  { ops := #[.let 1 (.const 0), .let 2 (.const 7), .stmt (.tstore 1 2), .let 3 (.tload 1),
      .let 4 (.const 3), .stmt (.sstore 4 3)],
    control := .stop }]

/-- A callee that sets slot 0 to 9 and every balance to 3. -/
def callee (st : Store) : World :=
  ⟨{ st with persistent := st.persistent.set 0 9 }, ⟨fun _ => 3, fun _ => .empty⟩⟩

def just (c : Expr VarId) : Program :=
  initOnly #[{ ops := #[.let 10 (.const 0), .let 11 (.const 1), .let 3 c], control := .stop }]

def runS (p : Program) (l : Layout p := by exact plainLayout _) : Run :=
  runInit p l (world := { after := callee })

def runStatic (p : Program) (l : Layout p := by exact plainLayout _)
    (imms : MainImmutables := noImmutables) : Run :=
  runMain p imms l (static := true)

def worldChecks : List (String × Bool) :=
  [ ("sload reads the frame's own sstore",
      (runS (storeAround (.const 0))).slots [0, 1, 2, 3] == [5, 5, 1, 0]),
    ("tload reads the frame's own tstore", (runS transient).slots [0, 1, 2, 3] == [0, 0, 0, 7]),
    ("after a call, storage and world are what the callee left",
      (runS (storeAround (.call 10 10 10 10 10 10 10))).slots [0, 1, 2, 3] == [9, 9, 3, 0]),
    ("after a delegatecall too",
      (runS (storeAround (.delegatecall 10 10 10 10 10 10))).slots [0, 1, 2, 3] == [9, 9, 3, 0]),
    ("after a create too (initcode may reenter)",
      (runS (storeAround (.create 10 10 10))).slots [0, 1, 2, 3] == [9, 9, 3, 0]),
    ("a staticcall changes nothing",
      (runS (storeAround (.staticcall 10 10 10 10 10 10))).slots [0, 1, 2, 3] == [5, 5, 1, 0]),
    ("a static frame halts at sstore", (runStatic (storeAround (.const 0))).result == .invalid),
    ("a static frame halts at tstore", (runStatic transient).result == .invalid),
    ("a static frame halts at create", (runStatic (just (.create 10 10 10))).result == .invalid),
    ("a static frame halts at a call with value",
      (runStatic (just (.call 10 10 11 10 10 10 10))).result == .invalid),
    ("a static frame may call without value",
      (runStatic (just (.call 10 10 10 10 10 10 10))).result == .ret []),
    ("revert discards storage", (runS revert).result == .revert [0xDE, 0xAD] && (runS revert).store.isNone) ]

#eval show IO Unit from do
  let failed := (checks ++ worldChecks).filter (!·.2)
  unless failed.isEmpty do
    throw (IO.userError s!"example checks failed: {failed.map (·.1)}")
  IO.println s!"{checks.length + worldChecks.length} example checks passed"

end SirTests.Examples
