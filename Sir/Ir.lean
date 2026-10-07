import Sir.Word

/-! The SIR AST, mirroring plankc's `sir-data` (`EthIRProgram`) minus static allocation and
`freeptr`. Blocks and functions live in program-wide arrays indexed by their ids, as in plankc. -/

namespace Sir

structure VarId where
  id : Nat
  deriving DecidableEq, Hashable, Repr

structure BlockId where
  id : Nat
  deriving DecidableEq, Repr

structure FunctionId where
  id : Nat
  deriving DecidableEq, Repr

structure DataId where
  id : Nat
  deriving DecidableEq, Repr

structure ImmutableId where
  id : Nat
  deriving DecidableEq, Repr

instance {n : Nat} : OfNat VarId n := ⟨⟨n⟩⟩
instance {n : Nat} : OfNat BlockId n := ⟨⟨n⟩⟩
instance {n : Nat} : OfNat FunctionId n := ⟨⟨n⟩⟩
instance {n : Nat} : OfNat DataId n := ⟨⟨n⟩⟩
instance {n : Nat} : OfNat ImmutableId n := ⟨⟨n⟩⟩

/-- A memory access width in bytes, `1..=32` (`mload<8n>` / `mstore<8n>`). -/
structure ByteSize where
  val : Nat
  valid : 1 ≤ val ∧ val ≤ 32 := by decide
  deriving DecidableEq

/-- The operations plankc lowers to a single EVM opcode (`as_literal_evm_op`). Operands are in
EVM stack order: the first input is the top of the stack. -/
inductive EvmOp
  | add | mul | sub | div | sdiv | mod | smod | addmod | mulmod | exp | signextend
  | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte | shl | shr | sar | clz
  | keccak256
  | address | balance | origin | caller | callvalue | calldataload | calldatasize | calldatacopy
  | codesize | codecopy | gasprice | extcodesize | extcodecopy | returndatasize | returndatacopy
  | extcodehash | gas
  | blockhash | coinbase | timestamp | number | difficulty | gaslimit | chainid | selfbalance
  | basefee | blobhash | blobbasefee
  | sload | sstore | tload | tstore
  | mcopy
  | log0 | log1 | log2 | log3 | log4
  | create | create2 | call | callcode | delegatecall | staticcall
  | «return» | stop | revert | invalid | selfdestruct
  deriving DecidableEq, Repr

inductive Operation
  | evm (op : EvmOp) (ins outs : Array VarId)
  | malloc (size out : VarId)
  | mallocany (size out : VarId)
  | mload (size : ByteSize) (ptr out : VarId)
  | mstore (size : ByteSize) (ptr value : VarId)
  | copy (src out : VarId)
  /-- Both `const` and `large_const`: they differ only in plankc's encoding. -/
  | const (value : Word) (out : VarId)
  | dataOffset (data : DataId) (out : VarId)
  | noop
  | icall (function : FunctionId) (ins outs : Array VarId)
  | icallNever (function : FunctionId) (ins : Array VarId)
  | runtimeStartOffset (out : VarId)
  | initEndOffset (out : VarId)
  | runtimeLength (out : VarId)
  | getImmutable (immutable : ImmutableId) (out : VarId)
  | setImmutable (immutable : ImmutableId) (runtimePtr value : VarId)

inductive Control
  | lastOpTerminates
  | iret
  | continuesTo (target : BlockId)
  | branches (condition : VarId) (nonZero zero : BlockId)
  | switch (condition : VarId) (cases : Array (Word × BlockId)) (fallback : Option BlockId)

structure Block where
  inputs : Array VarId := #[]
  outputs : Array VarId := #[]
  ops : Array Operation := #[]
  control : Control

inductive ReturnKind
  | never
  | values (count : Nat)

structure Function where
  entry : BlockId
  returns : ReturnKind

structure Program where
  init : FunctionId
  main : Option FunctionId
  functions : Array Function
  blocks : Array Block
  data : Array ByteArray := #[]
  immutables : Array ByteSize := #[]

inductive Entry
  | init
  | main
  deriving DecidableEq, Repr

/-- Facts about the compiled bytecode that SIR can observe. They are fixed by the compiler, not
by the environment, so they are a parameter of the semantics rather than effects. -/
structure Layout where
  /-- Code offset of a data segment in the code object running `Entry`. -/
  dataOffset : Entry → DataId → Word
  runtimeStartOffset : Word
  initEndOffset : Word
  runtimeLength : Word
  /-- Placeholder offsets of an immutable, relative to the start of the runtime code. -/
  immutableRefs : ImmutableId → List Nat

/-- What the compiler must guarantee about a `Layout` for the init and runtime code it emits. -/
def Layout.Consistent (p : Program) (l : Layout) (initCode runtimeCode : ByteArray) : Prop :=
  l.initEndOffset.toNat = initCode.size ∧
  l.runtimeStartOffset.toNat + l.runtimeLength.toNat ≤ initCode.size ∧
  (∀ (d : DataId) (h : d.id < p.data.size),
    initCode.slicePad (l.dataOffset .init d).toNat p.data[d.id].size = p.data[d.id] ∧
    runtimeCode.slicePad (l.dataOffset .main d).toNat p.data[d.id].size = p.data[d.id]) ∧
  (∀ (i : ImmutableId) (h : i.id < p.immutables.size), ∀ r ∈ l.immutableRefs i,
    r + p.immutables[i.id].val ≤ l.runtimeLength.toNat)

end Sir
