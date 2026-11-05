import Sir.Eval
import Host.Interp
import ITree.Run

/-! A concrete test host: a fixed `Env`, the world operations of `interpHost` answered from a small
world, and deterministic placement (bump from `0x80`, zero bytes). `run` interprets memory and
host state, then runs the result. -/

namespace SirTests

open Sir Host

inductive Result
  | ret (data : List UInt8)
  | revert (data : List UInt8)
  | invalid
  | selfdestruct (beneficiary : Address)
  | malformed
  | ub (u : UB)
  | hostError (msg : String)
  | outOfFuel
  deriving DecidableEq, Repr

def startState : World := ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun _ => 1, fun _ => .empty⟩⟩

structure World where
  start : World := startState
  after : Store → World := fun st => { startState with store := st }
  callResult : Bool × ByteArray := (true, .empty)
  logs : Array (List Word × List UInt8) := #[]
  calls : Array (CallKind × Address × List UInt8) := #[]
  ops : Nat := 0

abbrev TestM := StateT World (Except String)

def countOp {α : Type} (v : α) : TestM α := do
  modify fun w => { w with ops := w.ops + 1 }
  pure v

def answer : (op : WorldOp) → TestM (WorldOp.Resp op)
  | .gas => countOp (1000000 : Word)
  | .log topics data => do
    modify fun w => { w with logs := w.logs.push (topics.toList, data.toList) }
    countOp ()
  | .call .staticcall _ account input _ => do
    modify fun w => { w with calls := w.calls.push (.staticcall, account, input.toList) }
    let w ← get
    countOp (w.callResult : Bool × ByteArray)
  | .call (.call value) _ account input st => do
    modify fun w => { w with calls := w.calls.push (.call value, account, input.toList) }
    let w ← get
    countOp ((w.callResult.1, w.callResult.2, w.after st) : Bool × ByteArray × World)
  | .call .delegatecall _ account input st => do
    modify fun w => { w with calls := w.calls.push (.delegatecall, account, input.toList) }
    let w ← get
    countOp ((w.callResult.1, w.callResult.2, w.after st) : Bool × ByteArray × World)
  | .create _ salt _ st => do
    let w ← get
    countOp (((if salt.isSome then 0xC2 else 0xC1 : Address), ByteArray.empty, w.after st) :
      Address × ByteArray × World)

/-- Places every allocation after the highest live one, from `0x80`. -/
def place : (c : MemoryND.Op) → TestM (MemoryND.Resp c)
  | .alloc size live _ => do
    let start := live.foldl (fun s a => max s a.end) 0x80
    let a : Allocation := ⟨Word.ofNat start, ⟨.replicate size.toNat 0⟩⟩
    if h : ValidAlloc live size.toNat a then pure ⟨a, h⟩ else throw "alloc"

def testEnv : Env where
  address := 0xA0
  origin := 7
  caller := 0xC0
  callvalue := 7
  gasprice := 7
  chainid := 1
  coinbase := 7
  timestamp := 7
  number := 7
  prevrandao := 7
  gaslimit := 7
  basefee := 7
  blobbasefee := 7
  blockhash _ := 7
  blobhash _ := 7

structure Run where
  result : Result
  store : Option Store
  world : World

def Run.slot (r : Run) (k : Word) : Word := (r.store.map (·.persistent k)).getD 0

def Run.slots (r : Run) (ks : List Word) : List Word := ks.map r.slot

def ofOutcome : UB ⊕ Outcome → Result × Option Store
  | .inl (.malformed _) => (.malformed, none)
  | .inl u => (.ub u, none)
  | .inr (.ret data st) => (.ret data.toList, some st)
  | .inr (.revert data) => (.revert data.toList, none)
  | .inr .invalid => (.invalid, none)
  | .inr (.selfdestruct a st) => (.selfdestruct a, some st)

def runWith (p : Program) (l : Layout p) (mode : ExecutionMode) (env : Env) (imm : Immutables p mode.kind)
    (world : World) (fuel : Nat) : Run :=
  match (CoFree.runM answer place fuel (interpHost env.address world.start (p.runHost l mode env imm))).run world with
  | .ok (none, w) => ⟨.outOfFuel, none, w⟩
  | .ok (some o, w) => let (r, st) := ofOutcome o; ⟨r, st, w⟩
  | .error msg => ⟨.hostError msg, none, world⟩

def plainLayout (p : Program) (hd : p.data.size = 0 := by decide)
    (hi : p.immutables.size = 0 := by decide) : Layout p where
  init := .empty
  init_u32 := by decide
  main := .empty
  main_u32 := by decide
  mainStartOffset := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  initDataOffsets i := absurd (Nat.lt_of_lt_of_eq i.isLt hd) (Nat.not_lt_zero _)
  mainDataOffsets i := absurd (Nat.lt_of_lt_of_eq i.isLt hd) (Nat.not_lt_zero _)
  immutableOffsets i := absurd (Nat.lt_of_lt_of_eq i.isLt hi) (Nat.not_lt_zero _)
  atLeastOne_immOffsets i := absurd (Nat.lt_of_lt_of_eq i.isLt hi) (Nat.not_lt_zero _)
  no_imm_imm_overlap i := absurd (Nat.lt_of_lt_of_eq i.isLt hi) (Nat.not_lt_zero _)
  no_imm_data_overlap d := absurd (Nat.lt_of_lt_of_eq d.isLt hd) (Nat.not_lt_zero _)

def noImmutables (p : Program) (hi : p.immutables.size = 0 := by decide) : MainImmutablesMap p :=
  ⟨⟨#[], hi.symm⟩, .empty, fun i => absurd (Nat.lt_of_lt_of_eq i.isLt hi) (Nat.not_lt_zero _)⟩

def runInit (p : Program) (l : Layout p := by exact plainLayout _) (env : Env := testEnv)
    (world : World := {}) (fuel : Nat := 100000) : Run :=
  runWith p l (.creation .empty) env .init world fuel

def runMain (p : Program) (imms : MainImmutablesMap p) (l : Layout p := by exact plainLayout _)
    (env : Env := testEnv) (static : Bool := false) (calldata : ByteArray := .empty)
    (world : World := {}) (fuel : Nat := 100000) : Run :=
  runWith p l (.call static calldata) env (.main imms) world fuel

end SirTests
