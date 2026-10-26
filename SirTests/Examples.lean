import SirTests.Host

namespace SirTests.Examples

open Sir Host

def b8 : ByteSize := ⟨1, by decide⟩
def b16 : ByteSize := ⟨2, by decide⟩
def b32bit : ByteSize := ⟨4, by decide⟩
def b32 : ByteSize := ⟨32, by decide⟩

def initOnly (blocks : Array Block) (extra : Array Function := #[]) : Program where
  init := 0
  main := none
  functions := #[⟨0, .never, blocks⟩] ++ extra

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
      .stmt (.sstore 22 6), .stmt (.sstore 23 8), .stmt (.log2 2 13 20 21), .let 30 (.const 0x10),
      .stmt (.mstore b8 30 20)],
    control := .stop }]

def oobRead : Program := initOnly #[
  { ops := #[.let 1 (.const 4), .let 2 (.malloc 1), .let 3 (.mload b32 2)],
    control := .stop }]

/-- Writes the first byte of a `mallocany`, reads it, then reads one unwritten byte too. -/
def uninitRead : Program := initOnly #[
  { ops := #[.let 1 (.const 32), .let 2 (.mallocany 1), .let 3 (.const 0xFF),
      .stmt (.mstore b8 2 3), .let 4 (.mload b8 2), .let 5 (.const 0), .stmt (.sstore 5 4),
      .let 6 (.mload b16 2)],
    control := .stop }]

/-- Copying unwritten bytes is fine; the copy is unwritten too. -/
def uninitCopy : Program := initOnly #[
  { ops := #[.let 1 (.const 32), .let 2 (.mallocany 1), .let 3 (.malloc 1), .stmt (.mcopy 3 2 1),
      .let 4 (.const 0), .stmt (.sstore 4 4), .let 5 (.mload b8 3)],
    control := .stop }]

def uninitReturn : Program := initOnly #[
  { ops := #[.let 1 (.const 4), .let 2 (.mallocany 1)], control := .return 2 1 }]

def outOfMemory : Program := initOnly #[
  { ops := #[.let 1 (.const 32), .let 2 (.malloc 1), .let 3 (.const (BitVec.allOnes 256)),
      .let 4 (.malloc 3)],
    control := .stop }]

def revert : Program := initOnly #[
  { ops := #[.let 1 (.const 2), .let 2 (.malloc 1), .let 3 (.const 0xDEAD),
      .stmt (.mstore b16 2 3)],
    control := .revert 2 1 }]

def spin : Program := initOnly #[{ control := .continuesTo 0 }]

def spinStoring : Program := initOnly #[
  { ops := #[.let 1 (.const 5), .stmt (.sstore 1 1)], control := .continuesTo 0 }]

def spinInCallee : Program := initOnly #[{ ops := #[.icall 1 #[] #[]], control := .stop }]
  (extra := #[⟨0, .values 0, #[{ control := .continuesTo 0 }]⟩])

def immLayout (refs : List Nat) : Layout := { noLayout with immutableRefs := fun _ => refs }

/-- `init` patches immutable 0 (2 bytes) into an 8-byte runtime copy; `main` reads it. -/
def immutables : Program where
  init := 0
  main := some 1
  functions := #[
    ⟨0, .never, #[
      { ops := #[.let 1 .runtimeLength, .let 2 (.malloc 1), .let 3 (.const 0xABCD),
          .stmt (.setImmutable 0 2 3)],
        control := .return 2 1 }]⟩,
    ⟨0, .never, #[
      { ops := #[.let 4 (.getImmutable 0), .let 5 (.const 0), .stmt (.sstore 5 4),
          .let 6 (.getImmutable 0), .let 7 (.const 1), .stmt (.sstore 7 6)],
        control := .stop }]⟩]
  immutables := #[b16]

def getImmutableInInit : Program :=
  let init : Function := ⟨0, .never, #[{ ops := #[.let 4 (.getImmutable 0)], control := .stop }]⟩
  { immutables with functions := immutables.functions.set! 0 init }

def calls : Program := initOnly #[
  { ops := #[.let 1 (.const 4), .let 2 (.malloc 1), .let 10 (.const 100), .let 11 (.const 0xBEEF),
      .let 12 (.const 0), .let 13 (.const 2), .let 3 (.call 10 11 12 2 12 2 13),
      .let 4 .returndatasize, .let 5 (.mload b16 2), .let 21 (.const 1), .let 22 (.const 2),
      .stmt (.sstore 12 3), .stmt (.sstore 21 4), .stmt (.sstore 22 5),
      .stmt (.returndatacopy 2 13 13)],
    control := .stop }]

/-- Allocates 4 bytes at `ptr` (var 2), sets var 14 := `ptr + 3`, var 15 := 2, then runs `ops`. -/
def withBuffer (ops : Array Operation) : Program := initOnly #[
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
    control := .selfdestruct 7 }] with data := #[⟨#[9]⟩] }

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

def undef (u : UB) : Outcome := .ub u

def malformed : Outcome := .invalid

def run (p : Program) (e : Entry := .init) (env : Env := testEnv) (world : World := {})
    (layout : Layout := noLayout) (imm : Array Word := #[]) (fuel : Nat := 100000) :
    Outcome × World :=
  runWith env world p layout (.ofWords p imm) e fuel

def runOut (p : Program) : Outcome × World := run p (world := { callResult := (true, ⟨#[1, 2, 3]⟩) })

def storage (r : Outcome × World) : List (Word × Word) := r.2.storage.reverse

def wordBytes (n : Nat) : List UInt8 := (Word.toBytes 32 (BitVec.ofNat 256 n)).toList

def checks : List (String × Bool) :=
  let mem := run memory
  let call := run calls (world := { callResult := (true, ⟨#[1, 2, 3]⟩) })
  let spun := run spinStoring (fuel := 1000)
  let env := run environment (env := { testEnv with calldata := ⟨#[1, 2, 3]⟩ })
  [ ("loop sums 0..9", (run loopSum).1 == .stop && storage (run loopSum) == [(0, 45)]),
    ("pure ops in stack order", (run pureOps).1 == .stop &&
      storage (run pureOps) == [(0, 7), (3, 80), (4, 1), (1, 1)]),
    ("icall returns (7, 12)", (run internalCall).1 == .ret (wordBytes 7 ++ wordBytes 12)),
    ("UB: out-of-allocation write", mem.1 == undef (.memoryOutOfBounds 0x10 1)),
    ("memory: mload8, partial mstore16, keccak, mcopy into mallocany",
      storage mem == ([(0, 0xAB), (1, (0xABBEEF : Word) <<< 232),
       (2, 0x3e889ef1ce94d5e823a41b0e65c5e971dcd08e9d92a3dff1038a5eeefc54f39d),
       (3, 0xABBEEF00)] : List (Word × Word))),
    ("UB: out-of-allocation read", (run oobRead).1 == undef (.memoryOutOfBounds 0x80 32)),
    ("UB: reading an unwritten mallocany byte",
      (run uninitRead).1 == undef (.uninitializedRead 0x80 2) && storage (run uninitRead) == [(0, 0xFF)]),
    ("UB: mcopy keeps bytes unwritten, reading the copy is UB",
      (run uninitCopy).1 == undef (.uninitializedRead 0xA0 1) && storage (run uninitCopy) == [(0, 0)]),
    ("UB: returning unwritten bytes", (run uninitReturn).1 == undef (.uninitializedRead 0x80 4)),
    ("UB: no placement for an allocation",
      (run outOfMemory).1 == undef (.outOfMemory (2 ^ 256 - 1))),
    ("memory: log2", mem.2.logs.toList == [([0, 1], [0xAB, 0xBE, 0xEF, 0])]),
    ("revert with data", (run revert).1 == .revert [0xDE, 0xAD]),
    ("divergence: out of fuel", (run spin (fuel := 1000)).1 == .outOfFuel),
    ("divergence: effects before it are observed", spun.1 == .outOfFuel && spun.2.storage.length > 10),
    ("divergence inside a callee", (run spinInCallee (fuel := 1000)).1 == .outOfFuel),
    ("setimmutable patches every placeholder",
      (run immutables (layout := immLayout [1, 5])).1 == .ret [0, 0xAB, 0xCD, 0, 0, 0xAB, 0xCD, 0]),
    ("setimmutable outside the runtime copy is UB",
      (run immutables (layout := immLayout [7])).1 == undef (.memoryOutOfBounds 0x87 2)),
    ("getimmutable: the run's fixed value, the same on every read, without host queries",
      let r := run immutables .main (imm := #[0x2345])
      r.1 == .stop && storage r == [(0, 0x2345), (1, 0x2345)] && r.2.queries == 0),
    ("Immutables.ofWords keeps the low size bytes",
      (Immutables.ofWords immutables #[0x12345])[(0 : ImmutableId)]? == some 0x2345),
    ("getimmutable in init is invalid", (run getImmutableInInit).1 == malformed),
    ("call: success, returndatasize, truncated return copy",
      storage call == [(0, 1), (1, 3), (2, 0x0102)]),
    ("call: request", call.2.calls.toList == [(.call 0, 0xBEEF, [])]),
    ("returndatacopy out of bounds is invalid", call.1 == .invalid),
    ("UB: call output written past the allocation",
      (runOut callOutputPastAlloc).1 == undef (.memoryOutOfBounds 0x83 2)),
    ("call writes only the bytes returned, not the whole requested range",
      (runOut callShortOutput).1 == .stop),
    ("UB: returndatacopy destination past the allocation",
      (runOut returnDataCopyPastAlloc).1 == undef (.memoryOutOfBounds 0x83 2)),
    ("returndatacopy source past the return data is invalid even if the destination is too",
      (runOut returnDataCopyPastBoth).1 == .invalid),
    ("switch takes the matching case", storage (run (switchOn 7)) == [(2, 2)]),
    ("UB: switch without match or fallback", (run (switchOn 9)).1 == undef .switchNoMatch),
    ("environment", env.1 == .selfdestruct 0xC0 && storage env ==
      ([(0, (0x0203 : Word) <<< 240), (1, 3), (2, 0x1000), (3, 0xC2), (4, 0xC0)] : List (Word × Word))),
    ("undefined variable is invalid", (run undefinedVar).1 == malformed),
    ("blocks are local to their function", (run foreignBlock).1 == malformed),
    ("icall_never: the callee halts", (run (neverCallee .never .stop)).1 == .stop),
    ("icall_never: the callee returning is invalid",
      (run (neverCallee (.values 0) .iret)).1 == malformed),
    ("returning from an entry is invalid",
      (run entryReturns).1 == malformed),
    ("an entry function declared to return values is invalid when it returns",
      (run entryReturnsValues).1 == malformed),
    ("missing main is invalid", (run loopSum .main).1 == malformed) ]

/-! Concrete storage (`exec`). -/

/-- `sstore 0 5`, then `c`, then `sstore 1 (sload 0)`, `sstore 2 (balance 0xB)`. -/
def storeAround (c : Expr VarId) (ops : Array Operation := #[]) : Program := initOnly #[
  { ops := #[.let 1 (.const 0), .let 2 (.const 5), .stmt (.sstore 1 2), .let 10 (.const 0)] ++ ops ++
      #[.let 3 c, .let 4 (.sload 1), .let 5 (.const 1), .stmt (.sstore 5 4), .let 6 (.const 0xB),
        .let 7 (.balance 6), .let 8 (.const 2), .stmt (.sstore 8 7)],
    control := .stop }]

def transient : Program := initOnly #[
  { ops := #[.let 1 (.const 0), .let 2 (.const 7), .stmt (.tstore 1 2), .let 3 (.tload 1),
      .let 4 (.const 3), .stmt (.sstore 4 3)],
    control := .stop }]

def startState : State := ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun _ => 1, fun _ => 0, fun _ => .empty⟩⟩

/-- A callee that sets slot 0 to 9 and every balance to 3. -/
def callee (st : Store) : State :=
  ⟨{ st with storage := st.storage.set 0 9 }, ⟨fun _ => 3, fun _ => 0, fun _ => .empty⟩⟩

def runS (p : Program) (env : Env := testEnv) : ExecOutcome :=
  runExec env startState callee p noLayout (.ofWords p #[]) .init

/-- The outcome, and slots `0..3` of the committed storage. -/
def slots : ExecOutcome → Option (Outcome × List Word)
  | .done o st => some (o, (st.map fun st => [0, 1, 2, 3].map st.storage).getD [])
  | .outOfFuel => none

def just (c : Expr VarId) : Program :=
  initOnly #[{ ops := #[.let 10 (.const 0), .let 11 (.const 1), .let 3 c], control := .stop }]

def staticEnv : Env := { testEnv with static := true }

def worldChecks : List (String × Bool) :=
  [ ("sload reads the frame's own sstore",
      slots (runS (storeAround (.const 0))) == some (.ret [], [5, 5, 1, 0])),
    ("tload reads the frame's own tstore", slots (runS transient) == some (.ret [], [0, 0, 0, 7])),
    ("after a call, storage and world are what the callee left",
      slots (runS (storeAround (.call 10 10 10 10 10 10 10))) == some (.ret [], [9, 9, 3, 0])),
    ("after a callcode too",
      slots (runS (storeAround (.callcode 10 10 10 10 10 10 10))) == some (.ret [], [9, 9, 3, 0])),
    ("after a delegatecall too",
      slots (runS (storeAround (.delegatecall 10 10 10 10 10 10))) == some (.ret [], [9, 9, 3, 0])),
    ("after a create too (initcode may reenter)",
      slots (runS (storeAround (.create 10 10 10))) == some (.ret [], [9, 9, 3, 0])),
    ("a staticcall changes nothing",
      slots (runS (storeAround (.staticcall 10 10 10 10 10 10))) == some (.ret [], [5, 5, 1, 0])),
    ("a static frame halts at sstore", slots (runS (storeAround (.const 0)) staticEnv) == some (.invalid, [])),
    ("a static frame halts at tstore", slots (runS transient staticEnv) == some (.invalid, [])),
    ("a static frame halts at create", slots (runS (just (.create 10 10 10)) staticEnv) == some (.invalid, [])),
    ("a static frame halts at a call with value",
      slots (runS (just (.call 10 10 11 10 10 10 10)) staticEnv) == some (.invalid, [])),
    ("a static frame may call without value, and the callee changes nothing",
      slots (runS (just (.call 10 10 10 10 10 10 10)) staticEnv) == some (.ret [], [0, 0, 0, 0])),
    ("revert discards storage", slots (runS revert) == some (.revert [0xDE, 0xAD], [])) ]

#eval show IO Unit from do
  let failed := (checks ++ worldChecks).filter (!·.2)
  unless failed.isEmpty do
    throw (IO.userError s!"example checks failed: {failed.map (·.1)}")
  IO.println s!"{checks.length + worldChecks.length} example checks passed"

end SirTests.Examples
