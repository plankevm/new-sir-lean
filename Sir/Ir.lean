import Sir.Word

/-! The SIR AST: plankc's `sir-data` (`EthIRProgram`) minus static allocation and `freeptr`, with
two structural changes. Each function owns its blocks, so a jump can only target a block of the
same function. Halting is a block's `Control`, so a block cannot halt mid-way or fall off its
end. -/

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

/-- Pure EVM operations with one input. -/
inductive UnOp
  | iszero | not | clz
  deriving DecidableEq, Repr

/-- Pure EVM operations with two inputs, `a` being the top of the EVM stack: `sub a b` is
`a - b`, `signextend b x`, `byte i x`, `shl shift x`. -/
inductive BinOp
  | add | mul | sub | div | sdiv | mod | smod | exp | signextend
  | lt | gt | slt | sgt | eq | and | or | xor | byte | shl | shr | sar
  deriving DecidableEq, Repr

/-- Pure EVM operations with three inputs, `a` being the top of the EVM stack: `addmod a b n`. -/
inductive TernOp
  | addmod | mulmod
  deriving DecidableEq, Repr

/-- The remaining non-halting operations plankc lowers to a single EVM opcode
(`as_literal_evm_op`): those touching memory, the environment or the host. Operands are in EVM stack order: the first input
is the top of the stack. -/
inductive EvmOp
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
  deriving DecidableEq, Repr

inductive Operation
  | unop (op : UnOp) (a out : VarId)
  | binop (op : BinOp) (a b out : VarId)
  | ternop (op : TernOp) (a b c out : VarId)
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
  | runtimeStartOffset (out : VarId)
  | initEndOffset (out : VarId)
  | runtimeLength (out : VarId)
  | getImmutable (immutable : ImmutableId) (out : VarId)
  | setImmutable (immutable : ImmutableId) (runtimePtr value : VarId)

/-- How a block ends. Block ids are local to the enclosing function. -/
inductive Control
  | iret
  | continuesTo (target : BlockId)
  | branches (condition : VarId) (nonZero zero : BlockId)
  | switch (condition : VarId) (cases : Array (Word × BlockId)) (fallback : Option BlockId)
  | stop
  | «return» (offset length : VarId)
  | revert (offset length : VarId)
  | invalid
  | selfdestruct (beneficiary : VarId)
  | icallNever (function : FunctionId) (ins : Array VarId)

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
  blocks : Array Block

structure Program where
  init : FunctionId
  main : Option FunctionId
  functions : Array Function
  data : Array ByteArray := #[]
  immutables : Array ByteSize := #[]

/-- The values `getimmutable` reads: fixed for a whole run, one per immutable, each fitting the
immutable's declared size. -/
structure Immutables (p : Program) where
  values : Array Word
  size_eq : values.size = p.immutables.size
  fits : ∀ (i : Nat) (h : i < values.size),
    values[i].toNat < 2 ^ (8 * (p.immutables[i]'(size_eq ▸ h)).val)

def Word.lowBytes (n : Nat) (w : Word) : Word := (w.setWidth (8 * n)).setWidth 256

theorem Word.lowBytes_lt (n : Nat) (w : Word) : (Word.lowBytes n w).toNat < 2 ^ (8 * n) := by
  simp only [Word.lowBytes, BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- Immutable `i` takes the low bytes of `ws[i]` (0 if absent). -/
def Immutables.ofWords (p : Program) (ws : Array Word) : Immutables p where
  values := p.immutables.mapIdx fun i s => Word.lowBytes s.val (ws[i]?.getD 0)
  size_eq := Array.size_mapIdx
  fits i h := by simp only [Array.getElem_mapIdx]; exact Word.lowBytes_lt _ _

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
