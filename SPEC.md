# SIR semantics on `CoFree`

The authoritative description of this package. It is an executable semantics of plankc's Sensei IR
(SIR), checked against `~/Documents/Plank/monorepo-plank` at `32710d2`
(`feat/sir-immutables-v2`), `plankc/sir/crates/data/src/operation/mod.rs` (`define_operations!`),
`plankc/sir/docs/{README,ir_text_format}.md` and the debug backend. Structure follows sir-lean
(`main` AST, `coinductive-semantics` evaluator) re-expressed on `../itree`.

Core Lean only, toolchain `v4.34.1`, depends on itree as a separate library: a Lake git
dependency on `git@github.com:Philogy/itree.git` pinned to `rev = 93dcc9e` (full hash in
`lakefile.toml` and `lake-manifest.json`). `lake build` builds the library and runs every gate
below.

## Modules

| Module | Contents |
|---|---|
| `Sir/Word.lean` | `Word := BitVec 256`, pure EVM arithmetic (`Word.div`, `sdiv`, `signextend`, `byte`, `sar`, `clz`, …), big-endian byte conversion, `ByteArray.slicePad`. |
| `Sir/Keccak.lean` | Keccak-256 in pure Lean, `Word.keccak256`. |
| `Sir/Ir.lean` | AST (`Program`, `Function`, `Block`, `Control`, `Operation`, `EvmOp`), `Immutables`, `Entry`, `Layout`, `Layout.Consistent`. |
| `Sir/Effect.lean` | Effects: `Mem`, `Host`, `SirE := Mem ⊕ₑ Host`; `Fault` (`Malformed`, `UB`), `Query`, `CallKind`, `Placement`. |
| `Sir/Eval.lean` | Evaluator: `evalFunction`, `runEntry : (p : Program) → Layout → Immutables p → Entry → CoFree SirE Empty`. |
| `Sir/Memory.lean` | Frame memory handler `handleMem`, and the semantics `exec : (p : Program) → Layout → Immutables p → Entry → CoFree Host Empty`. |
| `Sir/Memory/Proofs.lean` | `placeable_iff`: the allocation check is exact. |
| `SirTests/` | Test host (`runWith`), pure-op and Keccak vectors, example programs, axiom audit. |

## AST

As in plankc: a `Program` has `init : FunctionId`, `main : Option FunctionId`, and program-wide
arrays of functions, blocks, data segments and immutable sizes. A `Function` is its entry block
and a `ReturnKind` (`never` or `values n`). A `Block` has `inputs`, `outputs`, `ops` and a
`Control`: `lastOpTerminates`, `iret`, `continuesTo`, `branches cond nonZero zero`, or
`switch cond cases fallback?`. Locals (`VarId`) hold `Word`s.

`Operation` has one constructor per non-EVM plankc operation, plus `evm op ins outs` for every
operation plankc lowers to one EVM opcode (`EvmOp`). EVM operands are in stack order: the first
input is the top of the stack (`emit_simple_operation` pushes inputs in reverse).

## Effects

`CoFree SirE` programs emit two kinds of operations.

`Mem` (frame-local, handled by `handleMem`): `alloc zeroed size : Word`,
`read offset length : ByteArray`, `write offset bytes : Unit`, `copy dst src length : Unit`,
`returnData : ByteArray`, `setReturnData bytes : Unit`.

`Host` (abstract; the EVM, the world, the deployed code):

| Op | Response | |
|---|---|---|
| `query q` | `Word` | `address`, `balance a`, `origin`, `caller`, `callvalue`, `gasprice`, `extcodehash a`, `gas`, `blockhash n`, `coinbase`, `timestamp`, `number`, `prevrandao`, `gaslimit`, `chainid`, `selfbalance`, `basefee`, `blobhash i`, `blobbasefee`, `sload k`, `tload k` |
| `sstore k v`, `tstore k v` | `Unit` | |
| `calldata`, `code`, `extcode a` | `ByteArray` | whole buffers; loads, sizes and copies are derived |
| `log topics data` | `Unit` | |
| `call kind gas account input` | `Bool × ByteArray` | success, return data; `kind` carries the value for `call`/`callcode` |
| `create value salt? initcode` | `Word × ByteArray` | address (0 on failure), return data |
| `alloc size live` | `{start // Placement live size start}` | the host places allocations; asked only when a placement exists, so it can always answer |
| `stop`, `ret data`, `revert data`, `invalid`, `selfdestruct a`, `fault f` | `Empty` | terminal; `fault` is the stuck state (see Faults) |

Gas exhaustion, static-context violations, call depth and the like are not SIR-level: a host
handler may end the run instead of answering any operation.

## Semantics

`runEntry p layout e` runs `init` or `main` (no `main` ⇒ malformed `noMain`). Internal calls are
`CoFree.fix` over `(FunctionId × Array Word) → Array Word`; a function body is `CoFree.iter` over
`(BlockId × Locals)`, with `Locals := Std.HashMap VarId Word` per activation. A block runs its
operations in order, then its control:

- `continuesTo`/`branches`/`switch`: the block's outputs are bound to the target's inputs.
  `branches` takes `nonZero` iff the condition is not 0. `switch` takes the first case equal to the
  condition, else the fallback, else UB `switchNoMatch` (plankc emits UB there).
- `iret`: returns the block's outputs; the count must match `values n`, and `never` functions
  must not return (malformed `returnKindMismatch`). Entry functions must not return
  (malformed `entryReturned`).
- `lastOpTerminates`: reaching the end of the block is malformed `fellThrough`.

Operations:

- Pure EVM operations compute in `Word`, with EVM conventions (division by zero is 0, shifts of
  256 or more saturate, `sdiv intMin (-1) = intMin`, `clz 0 = 256`).
- Environment and world reads are `Host` queries; `calldataload`/`calldatasize`/`calldatacopy`,
  `codesize`/`codecopy`, `extcodesize`/`extcodecopy` slice the whole buffer, zero-padded.
- Memory operations read and write through `Mem`. `mload<8n>`/`mstore<8n>` access exactly `n`
  bytes big-endian (low `n` bytes of the value). `keccak256`, `log*`, `return`, `revert`, `create*`
  and call arguments read memory; calls write `min(retLen, |output|)` bytes of output and set the
  return data; creates set the return data. Writes follow "Memory bounds" below.
- `icall` runs the callee and binds its results; `icall_never` runs the callee and faults if it
  returns.
- `const`, `copy`, `noop` are local. `data_offset`, `runtime_start_offset`, `init_end_offset`,
  `runtime_length` read the `Layout` (a parameter, fixed by the compiler, not an effect);
  `runtime_start_offset` and `init_end_offset` are malformed (`wrongEntry`) outside `init`.
- `getimmutable i` (main only, else malformed `wrongEntry`) returns `imm.values[i]`, where
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
accesses touch nothing. `alloc` asks the host for a placement only if one exists; otherwise it
is out of memory. Placements have no alignment: `Placement live size s` is
`s + size ≤ 2^256` and disjointness from every live allocation. `placeable` tries only 0 and the
end of each live allocation; `Proofs.placeable_iff` proves this exact (a placement slides down to
the highest allocation end at or below it, or to 0), so `outOfMemory` means no placement exists.

### Memory bounds and return data

- Writing any byte outside every allocation is UB (`memoryOutOfBounds`), for every writer:
  `mstore`, `mcopy` destination, `calldatacopy`/`codecopy`/`extcodecopy`/`returndatacopy`
  destination, the output a call writes, and `setimmutable`. A call writes only the
  `min(retLen, |output|)` bytes it actually returns (as in the EVM), so only those must be in
  bounds.
- `returndatacopy` reading past the end of the return data (`off + len > returndatasize`) is the
  normal EVM `invalid` halt, not UB, and is checked before the destination write, so it is
  `invalid` even when the destination is also out of bounds. Rationale: a program may check the
  return data size once and rely on that bound to keep later copies inside the memory it
  allocated; the EVM-level check then guards its memory safety, and a compiler must preserve the
  halt rather than assume it away.

`exec p layout e : CoFree Host Empty` is the semantics of an entry point. `Layout.Consistent`
states what the compiler must guarantee about the layout (data segments at their offsets, the
runtime slice and placeholders in bounds, `init_end_offset` = init code size); it is an assumption
for compiler proofs, not checked at run time.

## Faults

There is one mechanism: the terminal host operation `fault f`, whose response type is `Empty`,
so no continuation exists and the run is stuck with no defined result. `f : Fault` is either
`.malformed m` or `.ub u`:

```lean
inductive Fault
  | malformed (m : Malformed)   -- a well-formed program never reaches these
  | ub (u : UB)                 -- undefined behavior, reachable by well-formed programs
```

A refinement statement treats a source run reaching any `fault` as allowing any target behavior
from that point. The split exists for the well-formedness theorem below.

| `Fault` | Kind | When | Static condition that excludes it |
|---|---|---|---|
| `undefinedVariable v` | malformed | a use of `v` with no value in the activation | every use is defined on every path to it |
| `invalidFunction f` | malformed | `icall`/`icall_never`/entry to a nonexistent function | function ids in range |
| `invalidBlock b` | malformed | jump to / entry block is a nonexistent block | block ids in range |
| `invalidData d` | malformed | `data_offset` of a nonexistent segment | data ids in range |
| `invalidImmutable i` | malformed | `get`/`setimmutable` of a nonexistent immutable | immutable ids in range |
| `arity expected actual` | malformed | input/output count mismatch at a jump, a call or a call's results | arities agree |
| `badOperands op n` | malformed | EVM op with the wrong number of inputs or outputs | per-op arity |
| `fellThrough b` | malformed | end of a `lastOpTerminates` block reached | its last op terminates (halting EVM op or `icall_never`) |
| `returnKindMismatch f` | malformed | `iret` in a `never` function, or with the wrong count | `iret` only in `values n` functions, with `n` outputs |
| `neverReturned f` | malformed | the callee of `icall_never` returned | `icall_never` targets `never` functions |
| `entryReturned` | malformed | an entry function returned | `init`/`main` are `never` |
| `noMain` | malformed | running `.main`, or `setimmutable`, without a `main` | `setimmutable` needs a `main`; the theorem only runs entries that exist |
| `wrongEntry` | malformed | `runtime_start_offset`/`init_end_offset`/`setimmutable` reachable from `main`, `getimmutable` from `init` | these ops are only in functions reachable from the allowed entry |
| `switchNoMatch` | UB | `switch` value matches no case, no fallback | (none: depends on the value) |
| `memoryOutOfBounds off len` | UB | read or write of a byte outside every allocation | (none) |
| `uninitializedRead off len` | UB | read of an unwritten `mallocany` byte | (none) |
| `outOfMemory size` | UB | no placement exists for an allocation | (none) |

Ambiguous cases, and the choice made: `switchNoMatch` is UB, not malformed, because whether a
case matches depends on a run-time value and plankc lowers it to UB. `noMain` for `.main` is
malformed rather than "the empty runtime" because SIR does not say what code a program without
`main` deploys; the intended theorem excludes it by hypothesis. `neverReturned` and `fellThrough`
are malformed because the static conditions in the last column exclude them even though the
callee itself may diverge or fault.

"Read" is any operation that observes memory contents as values: `mload`, `keccak256`, `log*`,
`return`, `revert`, `create*` initcode and call arguments. Unwritten `mallocany` bytes are
modeled as `none` rather than as host-chosen bytes because no SIR program may depend on them:
with arbitrary bytes, a program reading them would have defined (nondeterministic) behavior that
a compiler would have to preserve; with `none`, a read is UB, which leaves the compiler free to
leave the memory uninitialized or reuse it. `mcopy` is the exception because copying bytes
does not depend on their values; it propagates `none`, and a later read of the copy is UB.

### Intended well-formedness theorem (not proved)

```lean
theorem wf_not_malformed (p : Program) (hp : p.WF) (layout : Layout) (imm : Immutables p)
    (e : Entry) (he : e = .init ∨ p.main.isSome) :
    ¬ (exec p layout imm e).Reaches fun op => ∃ m, op = .fault (.malformed m)
```

where `Reaches P t` (to be defined) holds if, for some sequence of host answers, `t` reaches an
operation satisfying `P` after finitely many steps. `layout` and `imm` are unconstrained:
`Layout.Consistent` is not needed, since layout values only flow into words. `Program.WF` does
not exist yet; it is the conjunction of the last column of the malformed rows: ids in range,
arities (jumps, calls and results, EVM ops), definedness of every use on every path,
return-kind discipline (`iret` vs `never`/`values n`, `icall_never` targets, entries `never`),
terminating last ops, and entry-restricted ops reachable only from their entry.

## Coverage of plankc operations (`32710d2`, 95 kinds)

| plankc `OperationKind` | Status |
|---|---|
| `Add` `Mul` `Sub` `Div` `SDiv` `Mod` `SMod` `AddMod` `MulMod` `Exp` `SignExtend` | modeled: `evm`, pure |
| `Lt` `Gt` `SLt` `SGt` `Eq` `IsZero` `And` `Or` `Xor` `Not` `Byte` `Shl` `Shr` `Sar` `Clz` | modeled: `evm`, pure |
| `Keccak256` | modeled: `evm`, memory read + pure Keccak |
| `Address` `Balance` `Origin` `Caller` `CallValue` `GasPrice` `ExtCodeHash` `Gas` | modeled: `evm`, host query |
| `CallDataLoad` `CallDataSize` `CallDataCopy` | modeled: `evm`, host `calldata` |
| `CodeSize` `CodeCopy` | modeled: `evm`, host `code` |
| `ExtCodeSize` `ExtCodeCopy` | modeled: `evm`, host `extcode` |
| `ReturnDataSize` `ReturnDataCopy` | modeled: `evm`, frame return data (`Mem`) |
| `BlockHash` `Coinbase` `Timestamp` `Number` `Difficulty` `GasLimit` `ChainId` `SelfBalance` `BaseFee` `BlobHash` `BlobBaseFee` | modeled: `evm`, host query (`Difficulty` is `prevrandao`) |
| `SLoad` `SStore` `TLoad` `TStore` | modeled: `evm`, host |
| `MemoryCopy` (`mcopy`) | modeled: `evm`, `Mem.copy` (moves byte states, unwritten stays unwritten) |
| `Log0` `Log1` `Log2` `Log3` `Log4` | modeled: `evm`, host `log` |
| `Create` `Create2` | modeled: `evm`, host `create` |
| `Call` `CallCode` `DelegateCall` `StaticCall` | modeled: `evm`, host `call` |
| `Return` `Stop` `Revert` `Invalid` `SelfDestruct` | modeled: `evm`, terminal host ops |
| `DynamicAllocZeroed` (`malloc`) | modeled: `Operation.malloc` |
| `DynamicAllocAnyBytes` (`mallocany`) | modeled: `Operation.mallocany`; bytes unwritten until written, reading them is UB |
| `MemoryLoad` (`mload<N>`) | modeled: `Operation.mload` |
| `MemoryStore` (`mstore<N>`) | modeled: `Operation.mstore` |
| `SetCopy` | modeled: `Operation.copy` |
| `SetSmallConst` `SetLargeConst` | modeled: both are `Operation.const` (they differ only in plankc's encoding) |
| `SetDataOffset` | modeled: `Operation.dataOffset`, from `Layout` |
| `Noop` | modeled: `Operation.noop` |
| `InternalCall` | modeled: `Operation.icall` |
| `InternalCallNever` | modeled: `Operation.icallNever` |
| `RuntimeStartOffset` `InitEndOffset` `RuntimeLength` | modeled: from `Layout` |
| `GetImmutable` | modeled: `Operation.getImmutable`, from the run's fixed `Immutables p` |
| `SetImmutable` | modeled: `Operation.setImmutable`, writes the low `size` bytes at each placeholder |
| `StaticAllocZeroed` `StaticAllocAnyBytes` (`salloc`, `sallocany`) | omitted: the frontend does not emit static allocation |
| `AcquireFreePointer` (`freeptr`) | omitted: exposes the allocator's free pointer, which the allocation-based memory model deliberately abstracts away |

Control (`Control`): `LastOpTerminates`, `InternalReturn`, `ContinuesTo`, `Branches`, `Switch`:
all modeled. Program parts: functions with `ReturnKind`, global blocks, data segments, immutables:
all modeled.

## Gates (`lake build`)

- `SirTests.Ops`: pure operations and Keccak-256 (vectors including one- and two-block inputs).
- `Sir.Memory.Proofs`: `placeable_iff` and `no_placement_of_not_placeable`.
- `SirTests.Examples`: example programs run on the test host (loop, internal call, memory and
  Keccak, logs, revert, divergence with and without effects and inside a callee, immutables
  including `getimmutable` returning the same fixed value on every read without host queries,
  calls and return data, switch, environment, faults, and each UB case: out-of-allocation read
  and write, unwritten `mallocany` read via `mload` and `return`, `mcopy` of unwritten bytes,
  out of memory, call output written past an allocation, `returndatacopy` destination past an
  allocation; and the defined cases: a call writing only its returned bytes of a larger `retLen`,
  `returndatacopy` source past the return data is `invalid` even with an out-of-bounds
  destination).
- `SirTests.Audit`: every `Sir` declaration uses only `propext`, `Quot.sound`,
  `Classical.choice` (no `sorry`).
