import Sir

/-! A concrete test host: a fixed `Env`, and `Host` operations answered from a small world, with
deterministic placement (bump from `0x80`). Terminal operations end the run with an
`Outcome`; the world survives because the state sits under the exception. -/

namespace SirTests

open Sir

inductive Outcome
  | stop
  | ret (data : List UInt8)
  | revert (data : List UInt8)
  | invalid
  | selfdestruct (beneficiary : Word)
  | fault (fault : Fault)
  | hostError (msg : String)
  | outOfFuel
  deriving DecidableEq, Repr

structure World where
  storage : List (Word × Word) := []
  transient : List (Word × Word) := []
  logs : Array (List Word × List UInt8) := #[]
  calls : Array (CallKind × Word × List UInt8) := #[]
  callResult : Bool × ByteArray := (true, .empty)
  queries : Nat := 0

def World.sload (w : World) (k : Word) : Word := ((w.storage.find? (·.1 == k)).map (·.2)).getD 0

def World.tload (w : World) (k : Word) : Word := ((w.transient.find? (·.1 == k)).map (·.2)).getD 0

abbrev HostM := ExceptT Outcome (StateM World)

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
  calldata := .empty
  code := .empty

def countQuery (v : Word) : HostM Word := do
  modify fun w => { w with queries := w.queries + 1 }
  pure v

def answer : (op : HostOp) → HostM (HostOp.Resp op)
  | .gas => countQuery 1000000
  | .selfbalance | .balance _ | .extcodehash _ => countQuery 7
  | .sload k => do
    let w ← get
    countQuery (w.sload k)
  | .tload k => do
    let w ← get
    countQuery (w.tload k)
  | .sstore k v => modify fun w => { w with storage := (k, v) :: w.storage }
  | .tstore k v => modify fun w => { w with transient := (k, v) :: w.transient }
  | .extcode _ => pure (⟨#[1, 2, 3]⟩ : ByteArray)
  | .log topics data => modify fun w => { w with logs := w.logs.push (topics.toList, data.toList) }
  | .call kind _ account input => do
    modify fun w => { w with calls := w.calls.push (kind, account, input.toList) }
    let w ← get
    pure w.callResult
  | .create _ salt _ => pure ((if salt.isSome then 0xC2 else 0xC1 : Word), ByteArray.empty)
  | .stop => throw .stop
  | .ret data => throw (.ret data.toList)
  | .revert data => throw (.revert data.toList)
  | .invalid => throw .invalid
  | .selfdestruct a => throw (.selfdestruct a)
  | .fault f => throw (.fault f)

/-- Places every allocation after the highest live one, from `0x80`. -/
def place : (c : Choice) → HostM (Choice.Resp c)
  | .placement size live _ => do
    let start := live.foldl (fun s a => max s (a.1 + a.2)) 0x80
    if h : Placement live size start then pure ⟨start, h⟩ else throw (.hostError "alloc")

def runWith (env : Env) (world : World) (p : Program) (layout : Layout) (imm : Immutables p)
    (e : Entry) (fuel : Nat := 100000) : Outcome × World :=
  match (CoFree.runM (E := Exec) answer place fuel (exec p layout imm env e)).run.run world with
  | (.ok none, w) => (.outOfFuel, w)
  | (.ok (some x), _) => nomatch x
  | (.error o, w) => (o, w)

def noLayout : Layout where
  dataOffset _ d := BitVec.ofNat 256 (0x1000 + d.id)
  runtimeStartOffset := 0x40
  initEndOffset := 0x200
  runtimeLength := 8
  immutableRefs _ := []

end SirTests
