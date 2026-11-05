import SirTests.Host

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
def loopSum : Program := initOnly #[
  { ops := #[.let 1 (.const 0), .let 2 (.const 0)], outputs := #[1, 2], control := .continuesTo 1 },
  { inputs := #[3, 4],
    ops := #[.let 5 (.binop .add 4 3), .let 6 (.const 1), .let 7 (.binop .add 3 6),
        .let 8 (.const 10), .let 9 (.binop .lt 7 8)],
    outputs := #[7, 5], control := .branches 9 1 2 },
  { inputs := #[10, 11], ops := #[.let 12 (.const 0), .stmt (.sstore 12 11)],
    control := .stop }]

/-- An internal call returning two values, whose results are returned as ABI words. -/
def internalCall : Program := initOnly
  #[{ ops := #[.let 1 (.const 3), .let 2 (.const 4), .icall 1 #[1, 2] #[3, 4], .let 5 (.const 64),
      .let 6 (.malloc 5), .stmt (.mstore b32 6 3), .let 7 (.const 32), .let 8 (.binop .add 6 7),
      .stmt (.mstore b32 8 4)],
      control := .return 6 5 }]
  (extra := #[⟨0, .values 2, #[
    { inputs := #[20, 21], ops := #[.let 22 (.binop .add 20 21), .let 23 (.binop .mul 20 21)],
      outputs := #[22, 23], control := .iret }]⟩])

def memory : Program := initOnly #[
  { ops := #[.let 1 (.const 32), .let 2 (.malloc 1), .let 3 (.const ((0xAB : Word) <<< 248)),
      .stmt (.mstore b32 2 3), .let 4 (.mload b8 2), .let 10 (.const 1),
      .let 11 (.binop .add 2 10), .let 12 (.const 0xBEEF), .stmt (.mstore b16 11 12),
      .let 5 (.mload b32 2), .let 6 (.keccak256 2 1), .let 13 (.const 4), .let 7 (.mallocany 1),
      .stmt (.mcopy 7 2 13), .let 8 (.mload b32bit 7), .let 20 (.const 0), .let 21 (.const 1),
      .let 22 (.const 2), .let 23 (.const 3), .stmt (.sstore 20 4), .stmt (.sstore 21 5),
      .stmt (.sstore 22 6), .stmt (.sstore 23 8), .stmt (.log2 2 13 20 21)],
    control := .stop }]

def oobWrite : Program := initOnly #[
  { ops := #[.let 20 (.const 0), .let 30 (.const 0x10), .stmt (.mstore b8 30 20)], control := .stop }]

def oobRead : Program := initOnly #[
  { ops := #[.let 1 (.const 4), .let 2 (.malloc 1), .let 3 (.mload b32 2)],
    control := .stop }]

def outOfMemory : Program := initOnly #[
  { ops := #[.let 1 (.const 32), .let 2 (.malloc 1), .let 3 (.const (BitVec.allOnes 256)),
      .let 4 (.malloc 3)],
    control := .stop }]

def revert : Program := initOnly #[
  { ops := #[.let 1 (.const 2), .let 2 (.malloc 1), .let 3 (.const 0xDEAD),
      .stmt (.mstore b16 2 3)],
    control := .revert 2 1 }]

def spin : Program := initOnly #[{ control := .continuesTo 0 }]

def spinLogging : Program := initOnly #[
  { ops := #[.let 1 (.const 0), .stmt (.log0 1 1)], control := .continuesTo 0 }]

def spinInCallee : Program := initOnly #[{ ops := #[.icall 1 #[] #[]], control := .stop }]
  (extra := #[⟨0, .values 0, #[{ control := .continuesTo 0 }]⟩])

/-- `init` patches immutable 0 (2 bytes) into an 8-byte runtime copy; `main` reads it. -/
def immutables : Program where
  init := 0
  main := 1
  functions := #[
    ⟨0, .never, #[
      { ops := #[.let 1 .mainLength, .let 2 (.malloc 1), .let 3 (.const 0xABCD),
          .stmt (.setImmutable 0 2 3)],
        control := .return 2 1 }]⟩,
    ⟨0, .never, #[
      { ops := #[.let 4 (.getImmutable 0), .let 5 (.const 0), .stmt (.sstore 5 4),
          .let 6 (.getImmutable 0), .let 7 (.const 1), .stmt (.sstore 7 6)],
        control := .stop }]⟩]
  mainDatas := []
  immutables := #[b16]

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

def getImmutableInInit : Program := initOnly #[{ ops := #[.let 4 (.getImmutable 0)], control := .stop }]

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

def switchOn (v : Word) : Program := initOnly #[
  { ops := #[.let 1 (.const v)], control := .switch 1 #[(1, 1), (7, 2)] none },
  { ops := #[.let 2 (.const 1), .stmt (.sstore 2 2)], control := .stop },
  { ops := #[.let 3 (.const 2), .stmt (.sstore 3 3)], control := .stop }]

def environment : Program := { initOnly #[
  { ops := #[
      .let 1 (.const 1), .let 2 (.calldataload 1), .let 3 .calldatasize, .let 4 (.dataOffset 0),
      .let 5 (.const 0), .let 6 (.create2 5 5 5 1), .let 7 (.query .caller),
      .let 11 (.const 1), .let 12 (.const 2), .let 13 (.const 3), .let 14 (.const 4),
      .stmt (.sstore 5 2), .stmt (.sstore 11 3), .stmt (.sstore 12 4),
      .stmt (.sstore 13 6), .stmt (.sstore 14 7)],
    control := .selfdestruct 7 }] with data := #[⟨#[9]⟩], mainDatas := [⟨0, by decide⟩] }

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

def undefinedVar : Program := initOnly #[
  { ops := #[.stmt (.sstore 1 2)], control := .stop }]

/-- `sub`, `shl` and `addmod` take their first input as the EVM top of stack. -/
def pureOps : Program := initOnly #[
  { ops := #[.let 1 (.const 10), .let 2 (.const 3), .let 3 (.const 0), .let 4 (.const 4),
      .let 5 (.binop .sub 1 2), .let 6 (.binop .shl 2 1), .let 7 (.ternop .addmod 1 2 4),
      .let 8 (.unop .iszero 3), .stmt (.sstore 3 5), .stmt (.sstore 2 6), .stmt (.sstore 4 7),
      .stmt (.sstore 8 8)],
    control := .stop }]

/-- Block ids are local: function 0 has one block, so block 1 is out of range even though
function 1 has a block 1. -/
def foreignBlock : Program :=
  initOnly #[{ control := .continuesTo 1 }]
    (extra := #[⟨0, .never, #[{ control := .stop }, { control := .stop }]⟩])

def neverCallee (returns : ReturnKind) (callee : Control VarId) : Program :=
  initOnly #[{ control := .icallNever 1 #[] }] (extra := #[⟨0, returns, #[{ control := callee }]⟩])

def entryReturns : Program := initOnly #[{ control := .iret }]

def entryReturnsValues : Program :=
  { initOnly #[] with functions := #[⟨0, .values 0, #[{ control := .iret }]⟩] }

def runOut (p : Program) (l : Layout p := by exact plainLayout _) : Run :=
  runInit p l (world := { callResult := (true, ⟨#[1, 2, 3]⟩) })

def wordBytes (n : Nat) : List UInt8 := (Word.toBytes b32 (BitVec.ofNat 256 n)).toList

def immValues : MainImmutablesMap immutables := ⟨#v[0x2345], .empty, fun | ⟨0, _⟩ => by decide +revert⟩

def checks : List (String × Bool) :=
  let mem := runInit memory
  let call := runOut (callsThen #[])
  let spun := runInit spinLogging (fuel := 1000)
  let env := runMain environment (noImmutables _) envLayout (calldata := ⟨#[1, 2, 3]⟩)
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
    ("UB: getimmutable in init", (runInit getImmutableInInit).result == .malformed),
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
    ("icall_never: the callee halts", (runInit (neverCallee .never .stop)).result == .ret []),
    ("UB: icall_never callee returning",
      (runInit (neverCallee (.values 0) .iret)).result == .malformed),
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
def callee (st : Store) : State :=
  ⟨{ st with storage := st.storage.set 0 9 }, ⟨fun _ => 3, fun _ => .empty⟩⟩

def just (c : Expr VarId) : Program :=
  initOnly #[{ ops := #[.let 10 (.const 0), .let 11 (.const 1), .let 3 c], control := .stop }]

def runS (p : Program) (l : Layout p := by exact plainLayout _) : Run :=
  runInit p l (world := { after := callee })

def runStatic (p : Program) (l : Layout p := by exact plainLayout _)
    (imms : MainImmutablesMap p := by exact noImmutables _) : Run :=
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
