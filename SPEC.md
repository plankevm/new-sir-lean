# SIR semantics on `CoFree`

The authoritative description of this package. It is an executable semantics of plankc's Sensei IR
(SIR), checked against `~/Documents/Plank/monorepo-plank` at `32710d2`
(`feat/sir-immutables-v2`), `plankc/sir/crates/data/src/operation/mod.rs` (`define_operations!`),
`plankc/sir/docs/{README,ir_text_format}.md` and the debug backend. Structure follows sir-lean
(`main` AST, `coinductive-semantics` evaluator) re-expressed on `../itree`.

Core Lean only, toolchain `v4.34.1`, depends on `../itree`. `lake build` builds the library and
runs every gate below.

## Modules

| Module | Contents |
|---|---|
| `Sir/Word.lean` | `Word := BitVec 256`, pure EVM arithmetic (`Word.div`, `sdiv`, `signextend`, `byte`, `sar`, `clz`, …), big-endian byte conversion, `ByteArray.slicePad`. |
| `Sir/Keccak.lean` | Keccak-256 in pure Lean, `Word.keccak256`. |
| `Sir/Ir.lean` | AST (`Program`, `Function`, `Block`, `Control`, `Operation`, `EvmOp`), `Entry`, `Layout`, `Layout.Consistent`. |
| `Sir/Effect.lean` | Effects: `Mem`, `Host`, `SirE := Mem ⊕ₑ Host`; `Fault`, `Query`, `CallKind`, `Placement`. |
| `Sir/Eval.lean` | Evaluator: `evalFunction`, `runEntry : Program → Layout → Entry → CoFree SirE Empty`. |
| `Sir/Memory.lean` | Frame memory handler `handleMem`, and the semantics `exec : Program → Layout → Entry → CoFree Host Empty`. |
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
`read offset length : ByteArray`, `write offset bytes : Unit`, `returnData : ByteArray`,
`setReturnData bytes : Unit`.

`Host` (abstract; the EVM, the world, the deployed code):

| Op | Response | |
|---|---|---|
| `query q` | `Word` | `address`, `balance a`, `origin`, `caller`, `callvalue`, `gasprice`, `extcodehash a`, `gas`, `blockhash n`, `coinbase`, `timestamp`, `number`, `prevrandao`, `gaslimit`, `chainid`, `selfbalance`, `basefee`, `blobhash i`, `blobbasefee`, `sload k`, `tload k`, `immutable i` |
| `sstore k v`, `tstore k v` | `Unit` | |
| `calldata`, `code`, `extcode a` | `ByteArray` | whole buffers; loads, sizes and copies are derived |
| `log topics data` | `Unit` | |
| `call kind gas account input` | `Bool × ByteArray` | success, return data; `kind` carries the value for `call`/`callcode` |
| `create value salt? initcode` | `Word × ByteArray` | address (0 on failure), return data |
| `alloc size live` | `{start // Placement live size start}` | the host places allocations; no valid answer = cannot continue |
| `anyByte` | `UInt8` | an arbitrary byte |
| `stop`, `ret data`, `revert data`, `invalid`, `selfdestruct a`, `fault f` | `Empty` | terminal |

Gas exhaustion, static-context violations, call depth and the like are not SIR-level: a host
handler may end the run instead of answering any operation.

## Semantics

`runEntry p layout e` runs `init` or `main` (no `main` ⇒ `fault noMain`). Internal calls are
`CoFree.fix` over `(FunctionId × Array Word) → Array Word`; a function body is `CoFree.iter` over
`(BlockId × Locals)`, with `Locals := Std.HashMap VarId Word` per activation. A block runs its
operations in order, then its control:

- `continuesTo`/`branches`/`switch`: the block's outputs are bound to the target's inputs.
  `branches` takes `nonZero` iff the condition is not 0. `switch` takes the first case equal to the
  condition, else the fallback, else `fault switchNoMatch` (plankc emits UB there).
- `iret`: returns the block's outputs; the count must match `values n`, and `never` functions
  must not return (`fault returnKindMismatch`). Entry functions must not return
  (`fault entryReturned`).
- `lastOpTerminates`: reaching the end of the block is `fault fellThrough`.

Operations:

- Pure EVM operations compute in `Word`, with EVM conventions (division by zero is 0, shifts of
  256 or more saturate, `sdiv intMin (-1) = intMin`, `clz 0 = 256`).
- Environment and world reads are `Host` queries; `calldataload`/`calldatasize`/`calldatacopy`,
  `codesize`/`codecopy`, `extcodesize`/`extcodecopy` slice the whole buffer, zero-padded.
- Memory operations read and write through `Mem`. `mload<8n>`/`mstore<8n>` access exactly `n`
  bytes big-endian (low `n` bytes of the value). `keccak256`, `log*`, `return`, `revert`, `create*`
  and call arguments read memory; calls write `min(retLen, |output|)` bytes of output and set the
  return data; creates set the return data. `returndatacopy` past the end of the return data is
  `invalid`.
- `icall` runs the callee and binds its results; `icall_never` runs the callee and faults if it
  returns.
- `const`, `copy`, `noop` are local. `data_offset`, `runtime_start_offset`, `init_end_offset`,
  `runtime_length` read the `Layout` (a parameter, fixed by the compiler, not an effect);
  `runtime_start_offset` and `init_end_offset` fault outside `init`.
- `getimmutable i` (main only, else `fault wrongEntry`) queries the host and keeps the low
  `size i` bytes. `setimmutable i ptr v` (init only, needs a `main`) writes the low `size i` bytes
  of `v` at `ptr + r` for every placeholder `r ∈ layout.immutableRefs i`; a bad `ptr` is caught
  only as an out-of-allocation write.

Memory (`handleMem`, state `FrameMem`): a list of allocations plus the return data buffer.
`malloc` allocations are zeroed; `mallocany` bytes are unknown until written. Reading an unknown
byte, or a byte outside every allocation, asks the host for `anyByte` on every read. Writing any
byte outside every allocation is undefined behavior: `fault (memoryOutOfBounds offset length)`.
Zero-length accesses touch nothing.

`exec p layout e : CoFree Host Empty` is the semantics of an entry point. `Layout.Consistent`
states what the compiler must guarantee about the layout (data segments at their offsets, the
runtime slice and placeholders in bounds, `init_end_offset` = init code size); it is an assumption
for compiler proofs, not checked at run time.

Faults (`Fault`) end a run without further observable effects. They cover malformed programs
(undefined locals, bad ids, arity mismatches, wrong entry for an operation) and undefined behavior
(out-of-allocation writes, switch without a match).

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
| `MemoryCopy` (`mcopy`) | modeled: `evm`, memory read then write |
| `Log0` `Log1` `Log2` `Log3` `Log4` | modeled: `evm`, host `log` |
| `Create` `Create2` | modeled: `evm`, host `create` |
| `Call` `CallCode` `DelegateCall` `StaticCall` | modeled: `evm`, host `call` |
| `Return` `Stop` `Revert` `Invalid` `SelfDestruct` | modeled: `evm`, terminal host ops |
| `DynamicAllocZeroed` (`malloc`) | modeled: `Operation.malloc` |
| `DynamicAllocAnyBytes` (`mallocany`) | modeled: `Operation.mallocany` |
| `MemoryLoad` (`mload<N>`) | modeled: `Operation.mload` |
| `MemoryStore` (`mstore<N>`) | modeled: `Operation.mstore` |
| `SetCopy` | modeled: `Operation.copy` |
| `SetSmallConst` `SetLargeConst` | modeled: both are `Operation.const` (they differ only in plankc's encoding) |
| `SetDataOffset` | modeled: `Operation.dataOffset`, from `Layout` |
| `Noop` | modeled: `Operation.noop` |
| `InternalCall` | modeled: `Operation.icall` |
| `InternalCallNever` | modeled: `Operation.icallNever` |
| `RuntimeStartOffset` `InitEndOffset` `RuntimeLength` | modeled: from `Layout` |
| `GetImmutable` `SetImmutable` | modeled |
| `StaticAllocZeroed` `StaticAllocAnyBytes` (`salloc`, `sallocany`) | omitted: the frontend does not emit static allocation |
| `AcquireFreePointer` (`freeptr`) | omitted: exposes the allocator's free pointer, which the allocation-based memory model deliberately abstracts away |

Control (`Control`): `LastOpTerminates`, `InternalReturn`, `ContinuesTo`, `Branches`, `Switch`:
all modeled. Program parts: functions with `ReturnKind`, global blocks, data segments, immutables:
all modeled.

## Gates (`lake build`)

- `SirTests.Ops`: pure operations and Keccak-256 (vectors including one- and two-block inputs).
- `SirTests.Examples`: example programs run on the test host (loop, internal call, memory and
  Keccak, logs, revert, divergence with and without effects and inside a callee, immutables,
  calls and return data, switch, environment, faults).
- `SirTests.Audit`: every `Sir` declaration uses only `propext`, `Quot.sound`,
  `Classical.choice` (no `sorry`).
