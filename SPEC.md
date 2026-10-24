# SIR semantics on `CoFree`

The authoritative description of this package. It is an executable semantics of plankc's Sensei IR
(SIR), checked against `~/Documents/Plank/monorepo-plank` at `32710d2`
(`feat/sir-immutables-v2`), `plankc/sir/crates/data/src/operation/mod.rs` (`define_operations!`),
`plankc/sir/docs/{README,ir_text_format}.md` and the debug backend. Structure follows sir-lean
(`main` AST, `coinductive-semantics` evaluator) re-expressed on `../itree`. The AST deliberately
departs from plankc's representation in three places (see "Deviations from plankc"); the set of
operations and their meaning do not.

Core Lean only, toolchain `v4.34.1`, depends on itree as a separate library: a Lake git
dependency on `git@github.com:Philogy/itree.git` pinned to `rev = 93dcc9e` (full hash in
`lakefile.toml` and `lake-manifest.json`). `lake build` builds the library and runs every gate
below.

## Modules

| Module | Contents |
|---|---|
| `Sir/Word.lean` | `Word := BitVec 256`, pure EVM arithmetic (`Word.div`, `sdiv`, `signextend`, `byte`, `sar`, `clz`, …), big-endian byte conversion, `ByteArray.slicePad`. |
| `Sir/Keccak.lean` | Keccak-256 in pure Lean, `Word.keccak256`. |
| `Sir/Ir.lean` | AST (`Program`, `Function`, `Block`, `Control`, `Operation`, `Expr`, `Stmt`, `Query`, `UnOp`, `BinOp`, `TernOp`, with hand-written `resolve` over operands), `Immutables`, `Entry`, `Layout`, `Layout.Consistent`. |
| `Sir/Effect.lean` | Effects: `Mem`, `Host`, `SirE := Mem ⊕ₑ Host` (no branches); `Choice` and `Exec` (`Host` operations plus `Choice` branches); `Fault` (`malformed`, `UB`), `CallKind`, `Placement`. |
| `Sir/Eval.lean` | `UnOp.eval`, `BinOp.eval`, `TernOp.eval`, `Expr.eval`, `Stmt.exec`; evaluator: `evalFunction`, `runEntry : (p : Program) → Layout → Immutables p → Entry → CoFree SirE Empty`. |
| `Sir/Memory.lean` | Frame memory handler `handleMem`, and the semantics `exec : (p : Program) → Layout → Immutables p → Entry → CoFree Exec Empty`. |
| `Sir/Memory/Proofs.lean` | `placeable_iff`: the allocation check is exact. |
| `Sir/Same.lean`, `Sir/Same/Proofs.lean` | `Same RR t₁ t₂` and `Deterministic t` on `exec` runs (see "Equivalence of runs"), and their lemmas. |
| `Sir/Outcome.lean`, `Sir/Outcome/Proofs.lean` | `Outcome`, `HasOutcome`, `Safe`, `Program.Safe` (see "Outcomes and safety"), and their lemmas. |
| `SirTests/` | Test host (`runWith`), pure-op and Keccak vectors, example programs, `Same` and `Safe` proofs on example programs (`kernel_rfl` computes runs in the kernel), axiom audit. |

## AST

A `Program` has `init : FunctionId`, `main : Option FunctionId`, and program-wide arrays of
functions, data segments and immutable sizes. A `Function` has an `entry : BlockId`, a
`ReturnKind` (`never` or `values n`) and its own `blocks : Array Block`; a `BlockId` indexes the
blocks of the enclosing function. A `Block` has `inputs`, `outputs`, `ops` and a `Control`:

| `Control` | |
|---|---|
| `iret` | return the block's outputs to the caller |
| `continuesTo t`, `branches cond nonZero zero`, `switch cond cases fallback?` | jump to a block of the same function |
| `stop`, `return off len`, `revert off len`, `invalid`, `selfdestruct beneficiary` | halt the run (the EVM halting opcodes, with their operands) |
| `icallNever f args` | call `f`, which must not return |

Locals (`VarId`) hold `Word`s.

Every non-halting plankc operation is an `Operation`, one of three forms:

```lean
inductive Operation
  | «let» (out : VarId) (e : Expr VarId)            -- exactly one output
  | icall (function : FunctionId) (ins outs : Array VarId)
  | stmt (s : Stmt VarId)                            -- no output
```

`Expr α` and `Stmt α` are parametric in their operands and have one constructor per plankc
operation with exact arity (no operand arrays), except that the environment reads with no input
and one word of output share `Expr.query (q : Query)`. `Control α` is parametric the same way.
Each has a `resolve` that takes a variable lookup `l : VarId → m Word` and replaces every operand
by its value, left to right; the evaluator resolves all operands of an operation once
(`e.resolve (lookup l)`) and then evaluates an `Expr Word` / executes a `Stmt Word`.

- `Expr`: pure word operations `unop (op : UnOp) a`, `binop (op : BinOp) a b`,
  `ternop (op : TernOp) a b c` (meaning: the pure total `UnOp.eval`, `BinOp.eval`,
  `TernOp.eval`); `const`, `copy`; `query q`; `balance`, `extcodehash`, `blockhash`, `blobhash`,
  `sload`, `tload`; `calldataload`, `calldatasize`, `codesize`, `extcodesize`, `returndatasize`;
  `keccak256`; `malloc`, `mallocany`, `mload`; `create`, `create2`; `call`, `callcode`,
  `delegatecall`, `staticcall`; `dataOffset`, `runtimeStartOffset`, `initEndOffset`,
  `runtimeLength`, `getImmutable`.
  - `UnOp`: `iszero` `not` `clz`
  - `BinOp`: `add` `mul` `sub` `div` `sdiv` `mod` `smod` `exp` `signextend` `lt` `gt` `slt`
    `sgt` `eq` `and` `or` `xor` `byte` `shl` `shr` `sar`
  - `TernOp`: `addmod` `mulmod`
  - `Query`: `address` `origin` `caller` `callvalue` `gasprice` `gas` `coinbase` `timestamp`
    `number` `prevrandao` `gaslimit` `chainid` `selfbalance` `basefee` `blobbasefee`
- `Stmt`: `mstore`, `mcopy`, `sstore`, `tstore`, `calldatacopy`, `codecopy`, `extcodecopy`,
  `returndatacopy`, `log0` … `log4`, `setImmutable`, `noop`.

Operands are in EVM stack order, as in plankc's `ins`: the first input is the top of the stack
(`emit_simple_operation` pushes inputs in reverse). So `binop .sub a b` is `a - b`,
`binop .shl s x` is `x << s`, `binop .byte i x` and `binop .signextend b x` take the index
first, and `ternop .addmod a b n` is `(a + b) % n`.

## Deviations from plankc

The AST is not a 1:1 port of plankc's `EthIRProgram`; two invariants plankc checks separately
are made structural so that the semantics and the well-formedness theorem need not mention them.

- **Function-owned blocks.** plankc keeps all blocks in one program-wide array and a function
  only names its entry block; which blocks belong to which function is implicit (reachability
  from the entry). Here each `Function` owns its blocks and block ids are local, so a jump to
  another function's block cannot be written, and two functions cannot share a block.
- **Explicit terminators.** plankc ends halting blocks with `Control::LastOpTerminates` and
  keeps the halting op (`return`, `stop`, `revert`, `invalid`, `selfdestruct`) or
  `icall_never` as the block's last `Operation`. Here those are `Control` constructors and are
  not operations, so a block cannot halt mid-way or fall off its end.
- **Exact-arity operations.** plankc stores every operation's inputs and outputs as index
  ranges into shared arrays, and the arity of a kind is a separate invariant. Here an operation
  is `let out e` (one output), `stmt s` (none) or `icall f ins outs`, and every `Expr`/`Stmt`
  constructor has exactly its operands as fields, so only jumps, internal calls and returns can
  have an arity mismatch. The no-input environment reads are grouped as `Expr.query`; inputs
  to `balance`, `sload` etc. are fields of their own constructors.

An importer from plankc maps a program onto this AST by:

1. Partitioning blocks by function: for each function, collect the blocks reachable from its
   entry through `ContinuesTo`/`Branches`/`Switch` and renumber them `0..n` (entry need not be
   0), rewriting jump targets. A block reachable from two functions is duplicated into each.
2. For each `LastOpTerminates` block, removing its last operation and making it the `Control`
   (`Return`/`Revert` with their two inputs, `SelfDestruct` with its one input, `Stop`,
   `Invalid`, `InternalCallNever` with its function and inputs). A `LastOpTerminates` block
   whose last op is not one of these, or a halting op that is not last, is rejected (in plankc
   these are malformed).
3. Mapping each remaining operation to `let out e` if its kind has exactly one output,
   `stmt s` if it has none, and `icall` for `InternalCall`, with operands taken positionally
   from `ins` (an operation with the wrong number of inputs or outputs for its kind is
   rejected).

## Effects

`CoFree SirE` programs emit two kinds of operations.

`Mem` (frame-local, handled by `handleMem`): `alloc zeroed size : Word`,
`read offset length : ByteArray`, `write offset bytes : Unit`, `copy dst src length : Unit`,
`returnData : ByteArray`, `setReturnData bytes : Unit`.

`Host` (abstract; the EVM, the world, the deployed code):

| Op | Response | |
|---|---|---|
| `query q` | `Word` | `q : Query`, the no-input environment reads |
| `balance a`, `extcodehash a`, `blockhash n`, `blobhash i`, `sload k`, `tload k` | `Word` | |
| `sstore k v`, `tstore k v` | `Unit` | |
| `calldata`, `code`, `extcode a` | `ByteArray` | whole buffers; loads, sizes and copies are derived |
| `log topics data` | `Unit` | |
| `call kind gas account input` | `Bool × ByteArray` | success, return data; `kind` carries the value for `call`/`callcode` |
| `create value salt? initcode` | `Word × ByteArray` | address (0 on failure), return data |
| `stop`, `ret data`, `revert data`, `invalid`, `selfdestruct a`, `fault f` | `Empty` | terminal; `fault` is the stuck state (see Faults) |

Gas exhaustion, static-context violations, call depth and the like are not SIR-level: a host
handler may end the run instead of answering any operation.

## Semantics

`runEntry p layout e` runs `init` or `main` (no `main` ⇒ malformed). Internal calls are
`CoFree.fix` over `(FunctionId × Array Word) → Array Word`; a function body is `CoFree.iter` over
`(BlockId × Locals)`, block ids resolved in the running function, with
`Locals := Std.TreeMap VarId Word` per activation (not a `HashMap`: its bucket index is a
`USize`, whose size the kernel cannot compute, so no concrete program would reduce in proofs).
A block runs its operations in order, then its control:

- `continuesTo`/`branches`/`switch`: the block's outputs are bound to the target's inputs.
  `branches` takes `nonZero` iff the condition is not 0. `switch` takes the first case equal to the
  condition, else the fallback, else UB `switchNoMatch` (plankc emits UB there).
- `iret`: returns the block's outputs; the count must match `values n`, and `never` functions
  must not return (malformed). An entry function that returns (possible
  only if it is declared `values n`) is malformed.
- `stop`, `invalid`: the terminal host operation of the same name. `return off len` and
  `revert off len` read `len` bytes of memory at `off` (a read, see Memory) and end with
  `ret`/`revert`; `selfdestruct a` ends with `selfdestruct a`.
- `icallNever f args`: runs `f` like `icall`; if it returns, malformed.

Operations (all operands of an operation are looked up before any of its effects, so an
undefined operand faults `malformed` before anything else the operation would do):

- Pure EVM operations compute in `Word`, with EVM conventions (division by zero is 0, shifts of
  256 or more saturate, `sdiv intMin (-1) = intMin`, `clz 0 = 256`).
- Environment and world reads are `Host` queries; `calldataload`/`calldatasize`/`calldatacopy`,
  `codesize`/`codecopy`, `extcodesize`/`extcodecopy` slice the whole buffer, zero-padded.
- Memory operations read and write through `Mem`. `mload<8n>`/`mstore<8n>` access exactly `n`
  bytes big-endian (low `n` bytes of the value). `keccak256`, `log*`, `create*`, call arguments
  and the `return`/`revert` controls read memory; calls write `min(retLen, |output|)` bytes of output and set the
  return data; creates set the return data. Writes follow "Memory bounds" below.
- `icall` runs the callee and binds its results.
- `returndatacopy` reading out of bounds halts with `invalid` mid-block (see below); it is the
  only operation that can halt, and only conditionally.
- `const`, `copy`, `noop` are local. `data_offset`, `runtime_start_offset`, `init_end_offset`,
  `runtime_length` read the `Layout` (a parameter, fixed by the compiler, not an effect);
  `runtime_start_offset` and `init_end_offset` are malformed outside `init`.
- `getimmutable i` (main only, else malformed) returns `imm.values[i]`, where
  `imm : Immutables p` is a parameter of the run, like `Layout`: chosen once before the run
  starts, so every read in a run sees the same value, and by construction each value fits the
  immutable's declared size (`Immutables.fits`; `Immutables.ofWords` builds one by keeping low
  bytes). It is not read from the code bytes and is not a host query.
- `setimmutable i ptr v` (init only, needs a `main`) writes the low `size i` bytes
  of `v` at `ptr + r` for every placeholder `r ∈ layout.immutableRefs i`; a bad `ptr` is caught
  only as an out-of-allocation write.

Memory (`handleMem`, state `FrameMem`): a list of allocations plus the return data buffer; each
byte is `some b` or `none` (unwritten). `malloc` bytes start as `some 0`, `mallocany` bytes as
`none`. `read` returns bytes only if every byte is allocated and written; `write` requires every
byte to be allocated; `copy` (`mcopy`) requires both ranges to be allocated and moves byte
states, so copying unwritten bytes is defined and the destination is unwritten. Zero-length
accesses touch nothing. `alloc` branches (`CoFree.choose (.placement size live fits)`, response
`{start // Placement live size start}`) over every valid placement if one exists, so the branch is
never empty (`fits` is the witness); otherwise it is UB `outOfMemory`. The host does not place
allocations: the branch passes through to `exec`'s result, and whoever runs it picks. Placements have no alignment: `Placement live size s` is
`s + size ≤ 2^256` and disjointness from every live allocation. `placeable` tries only 0 and the
end of each live allocation; `Proofs.placeable_iff` proves this exact (a placement slides down to
the highest allocation end at or below it, or to 0), so `outOfMemory` means no placement exists.

### Memory bounds and return data

- Writing any byte outside every allocation is UB (`memoryOutOfBounds`), for every writer:
  `mstore`, `mcopy` destination, `calldatacopy`/`codecopy`/`extcodecopy`/`returndatacopy`
  destination, the output a call writes, and `setimmutable`.
- A call writes only the `min(retLen, |output|)` bytes it actually returns (as in the EVM), so
  only those must be in bounds. A `retLen` larger than the allocation at `retOffset` is not
  itself UB: it is UB only if the call returns more bytes than fit. Calls are host operations,
  so a proof about a program quantifies over every possible response anyway, including the
  long ones.
- `returndatacopy` reading past the end of the return data (`off + len > returndatasize`) is the
  normal EVM `invalid` halt, not UB, and is checked before the destination write, so it is
  `invalid` even when the destination is also out of bounds. Rationale: a program may check the
  return data size once and rely on that bound to keep later copies inside the memory it
  allocated; the EVM-level check then guards its memory safety, and a compiler must preserve the
  halt rather than assume it away.

`exec p layout e : CoFree Exec Empty` is the semantics of an entry point; `Exec` has the `Host`
operations and the `Choice` branches. `Layout.Consistent`
states what the compiler must guarantee about the layout (data segments at their offsets, the
runtime slice and placeholders in bounds, `init_end_offset` = init code size); it is an assumption
for compiler proofs, not checked at run time.

## Faults

There is one mechanism: the terminal host operation `fault f`, whose response type is `Empty`,
so no continuation exists and the run is stuck with no defined result. `f : Fault` is either
`.malformed` or `.ub u`:

```lean
inductive Fault
  | malformed     -- a well-formed program never reaches this
  | ub (u : UB)   -- undefined behavior, reachable by well-formed programs
```

`Same` (below) treats both as ordinary visible operations: a fault relates only to the same
fault, payload included. The split exists for the well-formedness theorem
below. `malformed` carries no
reason: the cases below are listed only to derive `Program.WF`.

| Case | `Fault` | When | Static condition that excludes it |
|---|---|---|---|
| undefined variable | `malformed` | a use of `v` with no value in the activation | every use is defined on every path to it |
| invalid function | `malformed` | `icall`/`icall_never`/entry to a nonexistent function | function ids in range |
| invalid block | `malformed` | jump to / entry block is a nonexistent block of `f` | block ids in range of their function's blocks |
| invalid data | `malformed` | `data_offset` of a nonexistent segment | data ids in range |
| invalid immutable | `malformed` | `get`/`setimmutable` of a nonexistent immutable | immutable ids in range |
| arity | `malformed` | input/output count mismatch at a jump, an internal call's arguments or its results | arities agree (other operations have exact arity and cannot reach this) |
| return kind mismatch | `malformed` | `iret` in a `never` function, or with the wrong count | `iret` only in `values n` functions, with `n` outputs |
| never-returning function returned | `malformed` | a function that must not return returned: the callee of `icall_never`, or an entry function | `icall_never` targets `never` functions; `init`/`main` are `never` |
| no `main` | `malformed` | running `.main`, or `setimmutable`, without a `main` | `setimmutable` needs a `main`; the theorem only runs entries that exist |
| wrong entry | `malformed` | `runtime_start_offset`/`init_end_offset`/`setimmutable` reachable from `main`, `getimmutable` from `init` | these ops are only in functions reachable from the allowed entry |
| `switchNoMatch` | UB | `switch` value matches no case, no fallback | (none: depends on the value) |
| `memoryOutOfBounds off len` | UB | read or write of a byte outside every allocation | (none) |
| `uninitializedRead off len` | UB | read of an unwritten `mallocany` byte | (none) |
| `outOfMemory size` | UB | no placement exists for an allocation | (none) |

Ambiguous cases, and the choice made: `switchNoMatch` is UB, not malformed, because whether a
case matches depends on a run-time value and plankc lowers it to UB. Running `.main` without a
`main` is malformed rather than "the empty runtime" because SIR does not say what code a program
without `main` deploys; the intended theorem excludes it by hypothesis. A function that must not
return returning is malformed because the static condition in the last column excludes it even
though the callee itself may diverge or fault.

Cases removed by the structural deviations: plankc-style programs could fall off the end of a
`LastOpTerminates` block (`fellThrough`), halt mid-block, or jump into another function's
blocks; none of these is expressible here, so there is no fault or WF condition for them.

"Read" is any operation that observes memory contents as values: `mload`, `keccak256`, `log*`,
the `return`/`revert` controls, `create*` initcode and call arguments. Unwritten `mallocany` bytes are
modeled as `none` rather than as host-chosen bytes because no SIR program may depend on them:
with arbitrary bytes, a program reading them would have defined (nondeterministic) behavior that
a compiler would have to preserve; with `none`, a read is UB, which leaves the compiler free to
leave the memory uninitialized or reuse it. `mcopy` is the exception because copying bytes
does not depend on their values; it propagates `none`, and a later read of the copy is UB.

### Intended well-formedness theorem (not proved)

```lean
theorem wf_not_malformed (p : Program) (hp : p.WF) (layout : Layout) (imm : Immutables p)
    (env : Env) (e : Entry) (he : e = .init ∨ p.main.isSome) :
    ¬HasOutcome (exec p layout imm env e) (.fault .malformed)
```

(`HasOutcome`: see "Outcomes and safety"). `layout` and `imm` are unconstrained:
`Layout.Consistent` is not needed, since layout values only flow into words. `Program.WF` does
not exist yet; it is the conjunction of the last column of the malformed rows: function, data
and immutable ids in range, block ids in range of their own function, arities (jumps, calls and
results), definedness of every use on every path, return-kind discipline (`iret` vs
`never`/`values n`, `icall_never` targets, entries `never`), and entry-restricted ops reachable
only from their entry. It has no condition on terminators or on which blocks a function may
jump to: the types rule those out.

## Coverage of plankc operations (`32710d2`, 95 kinds)

| plankc `OperationKind` | Status |
|---|---|
| `IsZero` `Not` `Clz` | modeled: `Expr.unop`, pure |
| `Add` `Mul` `Sub` `Div` `SDiv` `Mod` `SMod` `Exp` `SignExtend` | modeled: `Expr.binop`, pure |
| `Lt` `Gt` `SLt` `SGt` `Eq` `And` `Or` `Xor` `Byte` `Shl` `Shr` `Sar` | modeled: `Expr.binop`, pure |
| `AddMod` `MulMod` | modeled: `Expr.ternop`, pure |
| `Keccak256` | modeled: `Expr.keccak256`, memory read + pure Keccak |
| `Address` `Origin` `Caller` `CallValue` `GasPrice` `Gas` | modeled: `Expr.query`, host `query` |
| `Balance` `ExtCodeHash` | modeled: `Expr.balance`, `Expr.extcodehash`, host ops of the same name |
| `CallDataLoad` `CallDataSize` `CallDataCopy` | modeled: `Expr`/`Expr`/`Stmt`, host `calldata` |
| `CodeSize` `CodeCopy` | modeled: `Expr`/`Stmt`, host `code` |
| `ExtCodeSize` `ExtCodeCopy` | modeled: `Expr`/`Stmt`, host `extcode` |
| `ReturnDataSize` `ReturnDataCopy` | modeled: `Expr`/`Stmt`, frame return data (`Mem`) |
| `Coinbase` `Timestamp` `Number` `Difficulty` `GasLimit` `ChainId` `SelfBalance` `BaseFee` `BlobBaseFee` | modeled: `Expr.query`, host `query` (`Difficulty` is `prevrandao`) |
| `BlockHash` `BlobHash` | modeled: `Expr.blockhash`, `Expr.blobhash`, host ops of the same name |
| `SLoad` `TLoad` / `SStore` `TStore` | modeled: `Expr` / `Stmt`, host ops of the same name |
| `MemoryCopy` (`mcopy`) | modeled: `Stmt.mcopy`, `Mem.copy` (moves byte states, unwritten stays unwritten) |
| `Log0` `Log1` `Log2` `Log3` `Log4` | modeled: `Stmt.log0` … `Stmt.log4`, host `log` |
| `Create` `Create2` | modeled: `Expr`, host `create` |
| `Call` `CallCode` `DelegateCall` `StaticCall` | modeled: `Expr`, host `call` |
| `Return` `Stop` `Revert` `Invalid` `SelfDestruct` | modeled: `Control` terminators, terminal host ops |
| `DynamicAllocZeroed` (`malloc`) | modeled: `Expr.malloc` |
| `DynamicAllocAnyBytes` (`mallocany`) | modeled: `Expr.mallocany`; bytes unwritten until written, reading them is UB |
| `MemoryLoad` (`mload<N>`) | modeled: `Expr.mload` |
| `MemoryStore` (`mstore<N>`) | modeled: `Stmt.mstore` |
| `SetCopy` | modeled: `Expr.copy` |
| `SetSmallConst` `SetLargeConst` | modeled: both are `Expr.const` (they differ only in plankc's encoding) |
| `SetDataOffset` | modeled: `Expr.dataOffset`, from `Layout` |
| `Noop` | modeled: `Stmt.noop` |
| `InternalCall` | modeled: `Operation.icall` |
| `InternalCallNever` | modeled: `Control.icallNever` |
| `RuntimeStartOffset` `InitEndOffset` `RuntimeLength` | modeled: from `Layout` |
| `GetImmutable` | modeled: `Expr.getImmutable`, from the run's fixed `Immutables p` |
| `SetImmutable` | modeled: `Stmt.setImmutable`, writes the low `size` bytes at each placeholder |
| `StaticAllocZeroed` `StaticAllocAnyBytes` (`salloc`, `sallocany`) | omitted: the frontend does not emit static allocation |
| `AcquireFreePointer` (`freeptr`) | omitted: exposes the allocator's free pointer, which the allocation-based memory model deliberately abstracts away |

Control: `InternalReturn`, `ContinuesTo`, `Branches`, `Switch` are modeled as `Control`
constructors; `LastOpTerminates` is replaced by the terminator constructors (see "Deviations
from plankc"). Program parts: functions with `ReturnKind`, blocks (owned by functions), data
segments, immutables: all modeled.

## Equivalence of runs

`CoFree.Same Ret` (in `ITree/Same.lean`) is a weak bisimulation: `Same Ret m₁ m₂` holds if
some relation `CoindRec` contains the pair and is closed under the one-layer inductive
`SameFinite Ret CoindRec`. Its rules: both return (`ret`, values related by `Ret`); both perform
the same operation (`impure`, `CoindRec` for every answer); both take an unobserved step
(`mutualUnobservedStep`, `CoindRec` for every pair of successors, via `ForallUnobserved`); and,
inductively, one side alone takes a `silent` step (`silentL`/`silentR`) or a branch for every
response (`branchL`/`branchR`), so only finitely many in a row and divergence is preserved. An
unobserved step is a `silent` or `branch` node; every operation is visible, and an operation
with no answer (a fault) relates only to the same operation, arguments included. `Same.coind`
is coinduction up to `Same`. Sanity theorems (`ITree/Same/Theorems.lean`, "Sanity checks"):
`spin` relates to `spin` and to no `pure`/`impure`; `pure a ~ pure b ↔ Ret a b`; a `silent`
step on either side is invisible; `impure` is related iff same op and related continuations;
an answerless op relates to itself; two branches are related iff every pair of responses is; a
response-ignoring branch is invisible; a branch whose responses are unrelated is not
self-related; `spin` relates to a branch into `spin`. `ITreeTests/Same.lean` proves a branch
printing the chosen number is not self-related, and not related to printing `0`.

Branches: `Effect` has, besides `Op`/`Resp`, branch ops `BrOp`/`BrResp` (none by default;
`⊕ₑ` sums both parts), and `Step`/`CoFree` have a `branch c k` node next to `impure`. A branch is a
choice nobody handles: `bind`, `iter`, `fixFrom` keep it, and `mapOps`, `interpState` and
`interp` pass it through via an `Effect.BrMap E F`; `run`/`runM`/`trace` take a `pick` for it.
`Bisim` matches it structurally (same `c`, related for every response). `Same` treats it as a
silent step quantified over every response, on each side independently, so `Deterministic`
means every branch behaves the same. Every branch has a response (`Effect.brResp_nonempty`,
discharged automatically for effects without branches or with inhabited responses), since a
`branch` with none would be related to everything; to get stuck, a semantics emits UB instead.
`Same.trans` holds outright; `Same.refl`/`Same.of_bisim` assume there are no
branches, because a program that observes a branch's response is not related to itself.
In SIR, only `handleMem` emits `branch` (allocation placement); the spec program `CoFree SirE` has none.

`Sir.Same RR t₁ t₂` instantiates it on `exec` runs (`CoFree Exec _`, `Mem` already handled):
every allocation is a placement branch, so a silent step taken with every valid placement,
independently on each side. A fault (`fault (.ub u)`, `fault .malformed`) relates only to the
same fault: UB of different kinds or arguments is not related (equivalence of SIR programs is
meant to be stated for programs that reach no UB). `Sir.Same2` is the relation written out
directly (`Same2F`: `tau`/`tauL`/`tauR` over `silent` and `branch`, `visible`, `ub`); its `ub`
rule still relates UB of any kind, so `same2_of_same` proves only `Same Eq → Same2`. Equivalence is stated only after
`Mem` is handled: on `CoFree SirE` an `alloc` is an ordinary operation. `Same` is a partial equivalence (symmetric and transitive), not an
equivalence: a run whose visible behavior depends on a placement (e.g. it stores a pointer) is
not related to itself. `Deterministic t := Same Eq t t` says that a run doesn't depend on placements.

## Outcomes and safety

`Sir/Outcome.lean`. An `exec` run has type `CoFree Exec Empty`, so it never returns; it ends at a
terminal host operation, which is its final result (no trace):

```lean
inductive Outcome
  | stop | ret (data : ByteArray) | revert (data : ByteArray) | invalid
  | selfdestruct (beneficiary : Word) | fault (f : Fault)
-- Outcome.op : Outcome → HostOp, the terminal operation of the same name

inductive HasOutcome : CoFree Exec Empty → Outcome → Prop
  | halt   : t.observe = .impure o.op k → HasOutcome t o
  | silent : t.observe = .silent t' → HasOutcome t' o → HasOutcome t o
  | branch (r) : t.observe = .branch c k → HasOutcome (k r) o → HasOutcome t o
  | impure (r) : t.observe = .impure op k → HasOutcome (k r) o → HasOutcome t o

def Safe (t : CoFree Exec Empty) : Prop :=
  (∀ u, ¬HasOutcome t (.fault (.ub u))) ∧ Deterministic t

def Program.Safe (p : Program) (layout : Layout) (e : Entry) : Prop :=
  ∀ imm env, Sir.Safe (exec p layout imm env e)
```

`HasOutcome t o`: for some host answers and some placements, `t` ends with `o` after finitely
many steps. A run with no outcome at all diverges on every path. `Safe` needs both halves: a run
with no UB outcome may still depend on placements (return a pointer), which `Deterministic`
rules out. Inputs are quantified in `Program.Safe`: frame data (calldata, caller, …) is the
`Env` argument and immutables the `Immutables p` argument, while everything the host answers
during the run is already covered by `HasOutcome`'s `impure` rule. The layout is fixed by the
compiler, so it is a parameter.

Theorems (`Sir/Outcome/Proofs.lean`): `HasOutcome.halt_iff` (at a terminal operation the outcome
is exactly that one), `silent_iff`, `branch_iff`/`impure_iff` (∃ response), `congr`,
`of_terminal`; `not_hasOutcome_spin`; `HasOutcome.of_same` and `Same.hasOutcome_iff`: runs
related by `Same` (any `Ret`) have the same outcomes, with no determinism assumption (a branch
on one side is related for every response, so whichever response reaches `o`, the other side
reaches it too); `Deterministic.hasOutcome_branch`: in a deterministic run every placement leads
to the same outcomes; `Safe.of_same`: a run related to a safe run is safe;
`not_safe_of_ub`, `not_safe_of_hasOutcome_ub`, `not_safe_of_branch_ub` (UB under one placement),
`not_safe_of_branch_outcomes` (placements with different outcomes, no UB needed); `safe_spin`.

## Gates (`lake build`)

- `SirTests.Ops`: pure operations and Keccak-256 (vectors including one- and two-block inputs).
- `Sir.Memory.Proofs`: `placeable_iff` and `no_placement_of_not_placeable`.
- `SirTests.Examples`: example programs run on the test host (loop, internal call, memory and
  Keccak, logs, revert, divergence with and without effects and inside a callee, immutables
  including `getimmutable` returning the same fixed value on every read without host queries,
  calls and return data, switch, environment, block ids local to their function, `icall_never`
  into a halting callee and into one that returns, an entry declared `values 0` returning,
  faults, and each UB case: out-of-allocation read and write, unwritten `mallocany` read via
  `mload` and `return`, `mcopy` of unwritten bytes, out of memory, call output written past an allocation, `returndatacopy` destination past an
  allocation; and the defined cases: a call writing only its returned bytes of a larger `retLen`,
  `returndatacopy` source past the return data is `invalid` even with an out-of-bounds
  destination).
- `SirTests.Same`: proved `Same`/not `Same` on example programs: allocations of different
  sizes, or on one side only, with the pointer unused; an extra jump; the same UB; two kinds of UB
  (not related); different stores; UB against `stop`; a program storing its pointer is not `Deterministic`.
- `SirTests.Safe`: `HasOutcome`/`Safe` on example programs: `stops` and `mallocs` are safe with
  outcome exactly `stop` (`mallocs` via `Safe.of_same`), `switchUB` and the pointer-storing `leaks`
  are not, and a run whose placement picks `stop` or `invalid` has no UB outcome but is not safe.
- `SirTests.Audit`: every declaration of `Sir`, `SirTests.Same`, `SirTests.Same2` and `SirTests.Safe` uses only `propext`,
  `Quot.sound`, `Classical.choice` (no `sorry`). `ITreeTests.Audit` does the same for `ITree`.
