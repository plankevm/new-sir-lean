import SirTests.Host

namespace SirTests.Examples

open Sir

def b8 : ByteSize := ⟨1, by decide⟩
def b16 : ByteSize := ⟨2, by decide⟩
def b32bit : ByteSize := ⟨4, by decide⟩
def b32 : ByteSize := ⟨32, by decide⟩

def ev (op : EvmOp) (ins outs : Array VarId) : Operation := .evm op ins outs

def initOnly (blocks : Array Block) (extra : Array Function := #[]) : Program where
  init := 0
  main := none
  functions := #[⟨0, .never⟩] ++ extra
  blocks := blocks

/-- `for i in 0..10: acc += i`, then `sstore 0 acc`. -/
def loopSum : Program := initOnly #[
  { ops := #[.const 0 1, .const 0 2], outputs := #[1, 2], control := .continuesTo 1 },
  { inputs := #[3, 4],
    ops := #[ev .add #[4, 3] #[5], .const 1 6, ev .add #[3, 6] #[7], .const 10 8, ev .lt #[7, 8] #[9]],
    outputs := #[7, 5], control := .branches 9 1 2 },
  { inputs := #[10, 11], ops := #[.const 0 12, ev .sstore #[12, 11] #[], ev .stop #[] #[]],
    control := .lastOpTerminates }]

/-- An internal call returning two values, whose results are returned as ABI words. -/
def internalCall : Program := initOnly (extra := #[⟨1, .values 2⟩]) #[
  { ops := #[.const 3 1, .const 4 2, .icall 1 #[1, 2] #[3, 4], .const 64 5, .malloc 5 6,
      .mstore b32 6 3, .const 32 7, ev .add #[6, 7] #[8], .mstore b32 8 4, ev .return #[6, 5] #[]],
    control := .lastOpTerminates },
  { inputs := #[20, 21], ops := #[ev .add #[20, 21] #[22], ev .mul #[20, 21] #[23]],
    outputs := #[22, 23], control := .iret }]

def memory : Program := initOnly #[
  { ops := #[
      .const 32 1, .malloc 1 2, .const ((0xAB : Word) <<< 248) 3, .mstore b32 2 3,
      .mload b8 2 4,
      .const 1 10, ev .add #[2, 10] #[11], .const 0xBEEF 12, .mstore b16 11 12,
      .mload b32 2 5,
      ev .keccak256 #[2, 1] #[6],
      .const 4 13, .mallocany 1 7, ev .mcopy #[7, 2, 13] #[], .mload b32bit 7 8,
      .const 0 20, .const 1 21, .const 2 22, .const 3 23,
      ev .sstore #[20, 4] #[], ev .sstore #[21, 5] #[], ev .sstore #[22, 6] #[],
      ev .sstore #[23, 8] #[],
      ev .log2 #[2, 13, 20, 21] #[],
      .const 0x10 30, .mstore b8 30 20],
    control := .lastOpTerminates }]

def oobRead : Program := initOnly #[
  { ops := #[.const 4 1, .malloc 1 2, .mload b32 2 3, ev .stop #[] #[]],
    control := .lastOpTerminates }]

/-- Writes the first byte of a `mallocany`, reads it, then reads one unwritten byte too. -/
def uninitRead : Program := initOnly #[
  { ops := #[.const 32 1, .mallocany 1 2, .const 0xFF 3, .mstore b8 2 3, .mload b8 2 4,
      .const 0 5, ev .sstore #[5, 4] #[], .mload b16 2 6, ev .stop #[] #[]],
    control := .lastOpTerminates }]

/-- Copying unwritten bytes is fine; the copy is unwritten too. -/
def uninitCopy : Program := initOnly #[
  { ops := #[.const 32 1, .mallocany 1 2, .malloc 1 3, ev .mcopy #[3, 2, 1] #[],
      .const 0 4, ev .sstore #[4, 4] #[], .mload b8 3 5, ev .stop #[] #[]],
    control := .lastOpTerminates }]

def uninitReturn : Program := initOnly #[
  { ops := #[.const 4 1, .mallocany 1 2, ev .return #[2, 1] #[]], control := .lastOpTerminates }]

def outOfMemory : Program := initOnly #[
  { ops := #[.const 32 1, .malloc 1 2, .const (BitVec.allOnes 256) 3, .malloc 3 4,
      ev .stop #[] #[]],
    control := .lastOpTerminates }]

def revert : Program := initOnly #[
  { ops := #[.const 2 1, .malloc 1 2, .const 0xDEAD 3, .mstore b16 2 3, ev .revert #[2, 1] #[]],
    control := .lastOpTerminates }]

def spin : Program := initOnly #[{ control := .continuesTo 0 }]

def spinStoring : Program := initOnly #[
  { ops := #[.const 5 1, ev .sstore #[1, 1] #[]], control := .continuesTo 0 }]

def spinInCallee : Program := initOnly (extra := #[⟨1, .values 0⟩]) #[
  { ops := #[.icall 1 #[] #[], ev .stop #[] #[]], control := .lastOpTerminates },
  { control := .continuesTo 1 }]

def immLayout (refs : List Nat) : Layout := { noLayout with immutableRefs := fun _ => refs }

/-- `init` patches immutable 0 (2 bytes) into an 8-byte runtime copy; `main` reads it. -/
def immutables : Program where
  init := 0
  main := some 1
  functions := #[⟨0, .never⟩, ⟨1, .never⟩]
  immutables := #[b16]
  blocks := #[
    { ops := #[.runtimeLength 1, .malloc 1 2, .const 0xABCD 3, .setImmutable 0 2 3,
        ev .return #[2, 1] #[]],
      control := .lastOpTerminates },
    { ops := #[.getImmutable 0 4, .const 0 5, ev .sstore #[5, 4] #[], .getImmutable 0 6,
        .const 1 7, ev .sstore #[7, 6] #[], ev .stop #[] #[]],
      control := .lastOpTerminates }]

def getImmutableInInit : Program :=
  let entry : Block := { ops := #[.getImmutable 0 4, ev .stop #[] #[]], control := .lastOpTerminates }
  { immutables with blocks := immutables.blocks.set! 0 entry }

def calls : Program := initOnly #[
  { ops := #[
      .const 4 1, .malloc 1 2, .const 100 10, .const 0xBEEF 11, .const 0 12, .const 2 13,
      ev .call #[10, 11, 12, 2, 12, 2, 13] #[3], ev .returndatasize #[] #[4], .mload b16 2 5,
      .const 1 21, .const 2 22,
      ev .sstore #[12, 3] #[], ev .sstore #[21, 4] #[], ev .sstore #[22, 5] #[],
      ev .returndatacopy #[2, 13, 13] #[]],
    control := .lastOpTerminates }]

def switchOn (v : Word) : Program := initOnly #[
  { ops := #[.const v 1], control := .switch 1 #[(1, 1), (7, 2)] none },
  { ops := #[.const 1 2, ev .sstore #[2, 2] #[], ev .stop #[] #[]], control := .lastOpTerminates },
  { ops := #[.const 2 3, ev .sstore #[3, 3] #[], ev .stop #[] #[]], control := .lastOpTerminates }]

def environment : Program := { initOnly #[
  { ops := #[
      .const 1 1, ev .calldataload #[1] #[2], ev .calldatasize #[] #[3], .dataOffset 0 4,
      .const 0 5, ev .create2 #[5, 5, 5, 1] #[6], ev .caller #[] #[7],
      .const 1 11, .const 2 12, .const 3 13, .const 4 14,
      ev .sstore #[5, 2] #[], ev .sstore #[11, 3] #[], ev .sstore #[12, 4] #[],
      ev .sstore #[13, 6] #[], ev .sstore #[14, 7] #[], ev .selfdestruct #[7] #[]],
    control := .lastOpTerminates }] with data := #[⟨#[9]⟩] }

def undefinedVar : Program := initOnly #[
  { ops := #[ev .sstore #[1, 2] #[]], control := .lastOpTerminates }]

def fallsThrough : Program := initOnly #[{ control := .lastOpTerminates }]

def entryReturns : Program := initOnly #[{ control := .iret }]

def run (p : Program) (e : Entry := .init) (world : World := {}) (layout : Layout := noLayout)
    (imm : Array Word := #[]) (fuel : Nat := 100000) : Outcome × World :=
  runWith world p layout (.ofWords p imm) e fuel

def storage (r : Outcome × World) : List (Word × Word) := r.2.storage.reverse

def wordBytes (n : Nat) : List UInt8 := (Word.toBytes 32 (BitVec.ofNat 256 n)).toList

def checks : List (String × Bool) :=
  let mem := run memory
  let call := run calls (world := { callResult := (true, ⟨#[1, 2, 3]⟩) })
  let spun := run spinStoring (fuel := 1000)
  let env := run environment (world := { calldata := ⟨#[1, 2, 3]⟩ })
  [ ("loop sums 0..9", (run loopSum).1 == .stop && storage (run loopSum) == [(0, 45)]),
    ("icall returns (7, 12)", (run internalCall).1 == .ret (wordBytes 7 ++ wordBytes 12)),
    ("UB: out-of-allocation write", mem.1 == .fault (.memoryOutOfBounds 0x10 1)),
    ("memory: mload8, partial mstore16, keccak, mcopy into mallocany",
      storage mem == ([(0, 0xAB), (1, (0xABBEEF : Word) <<< 232),
       (2, 0x3e889ef1ce94d5e823a41b0e65c5e971dcd08e9d92a3dff1038a5eeefc54f39d),
       (3, 0xABBEEF00)] : List (Word × Word))),
    ("UB: out-of-allocation read", (run oobRead).1 == .fault (.memoryOutOfBounds 0x80 32)),
    ("UB: reading an unwritten mallocany byte",
      (run uninitRead).1 == .fault (.uninitializedRead 0x80 2) && storage (run uninitRead) == [(0, 0xFF)]),
    ("UB: mcopy keeps bytes unwritten, reading the copy is UB",
      (run uninitCopy).1 == .fault (.uninitializedRead 0xA0 1) && storage (run uninitCopy) == [(0, 0)]),
    ("UB: returning unwritten bytes", (run uninitReturn).1 == .fault (.uninitializedRead 0x80 4)),
    ("UB: no placement for an allocation",
      (run outOfMemory).1 == .fault (.outOfMemory (2 ^ 256 - 1))),
    ("memory: log2", mem.2.logs.toList == [([0, 1], [0xAB, 0xBE, 0xEF, 0])]),
    ("revert with data", (run revert).1 == .revert [0xDE, 0xAD]),
    ("divergence: out of fuel", (run spin (fuel := 1000)).1 == .outOfFuel),
    ("divergence: effects before it are observed", spun.1 == .outOfFuel && spun.2.storage.length > 10),
    ("divergence inside a callee", (run spinInCallee (fuel := 1000)).1 == .outOfFuel),
    ("setimmutable patches every placeholder",
      (run immutables (layout := immLayout [1, 5])).1 == .ret [0, 0xAB, 0xCD, 0, 0, 0xAB, 0xCD, 0]),
    ("setimmutable outside the runtime copy is UB",
      (run immutables (layout := immLayout [7])).1 == .fault (.memoryOutOfBounds 0x87 2)),
    ("getimmutable: the run's fixed value, the same on every read, without host queries",
      let r := run immutables .main (imm := #[0x2345])
      r.1 == .stop && storage r == [(0, 0x2345), (1, 0x2345)] && r.2.queries == 0),
    ("Immutables.ofWords keeps the low size bytes",
      (Immutables.ofWords immutables #[0x12345]).values == #[0x2345]),
    ("getimmutable in init faults", (run getImmutableInInit).1 == .fault .wrongEntry),
    ("call: success, returndatasize, truncated return copy",
      storage call == [(0, 1), (1, 3), (2, 0x0102)]),
    ("call: request", call.2.calls.toList == [(.call 0, 0xBEEF, [])]),
    ("returndatacopy out of bounds is invalid", call.1 == .invalid),
    ("switch takes the matching case", storage (run (switchOn 7)) == [(2, 2)]),
    ("switch without match or fallback faults", (run (switchOn 9)).1 == .fault .switchNoMatch),
    ("environment", env.1 == .selfdestruct 0xC0 && storage env ==
      ([(0, (0x0203 : Word) <<< 240), (1, 3), (2, 0x1000), (3, 0xC2), (4, 0xC0)] : List (Word × Word))),
    ("undefined variable faults", (run undefinedVar).1 == .fault (.undefinedVariable 1)),
    ("falling through a terminating block faults", (run fallsThrough).1 == .fault (.fellThrough 0)),
    ("returning from an entry faults",
      (run entryReturns).1 == .fault (.returnKindMismatch 0)),
    ("missing main faults", (run loopSum .main).1 == .fault .noMain) ]

#eval show IO Unit from do
  let failed := checks.filter (!·.2)
  unless failed.isEmpty do
    throw (IO.userError s!"example checks failed: {failed.map (·.1)}")
  IO.println s!"{checks.length} example checks passed"

end SirTests.Examples
