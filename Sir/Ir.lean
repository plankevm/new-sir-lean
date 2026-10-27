import Host.Word
import Host.NatRange

/-! The SIR AST: plankc's `sir-data` (`EthIRProgram`) minus static allocation and `freeptr`, with
three structural changes. Each function owns its blocks, so a jump can only target a block of the
same function. Halting is a block's `Control`, so a block cannot halt mid-way or fall off its
end. Every operation has exact arity: it is an `Expr` bound to one local, a `Stmt` with no
output, or an internal call. -/

namespace Sir

structure VarId where
  id : Nat
  deriving DecidableEq, Ord, Repr

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

/-- Environment reads with no inputs and one word of output. -/
inductive Query
  | address | origin | caller | callvalue | gasprice | gas
  | coinbase | timestamp | number | prevrandao | gaslimit | chainid | selfbalance | basefee
  | blobbasefee
  deriving DecidableEq, Repr

/-- Operations with exactly one output, over operands of type `α`. Operands are in EVM stack
order: the first is the top of the stack. -/
inductive Expr (α : Type)
  | unop (op : UnOp) (a : α)
  | binop (op : BinOp) (a b : α)
  | ternop (op : TernOp) (a b c : α)
  /-- Both `const` and `large_const`: they differ only in plankc's encoding. -/
  | const (value : Word)
  | copy (src : α)
  | query (q : Query)
  | balance (account : α)
  | extcodehash (account : α)
  | blockhash (number : α)
  | blobhash (index : α)
  | sload (key : α)
  | tload (key : α)
  | calldataload (offset : α)
  | calldatasize
  | codesize
  | extcodesize (account : α)
  | returndatasize
  | keccak256 (offset length : α)
  | malloc (size : α)
  | mallocany (size : α)
  | mload (size : ByteSize) (ptr : α)
  | create (value offset length : α)
  | create2 (value offset length salt : α)
  | call (gas account value argsOffset argsLength retOffset retLength : α)
  | callcode (gas account value argsOffset argsLength retOffset retLength : α)
  | delegatecall (gas account argsOffset argsLength retOffset retLength : α)
  | staticcall (gas account argsOffset argsLength retOffset retLength : α)
  | dataOffset (data : DataId)
  | runtimeStartOffset
  | initEndOffset
  | runtimeLength
  | getImmutable (immutable : ImmutableId)

/-- Operations with no output, over operands of type `α`, in EVM stack order. -/
inductive Stmt (α : Type)
  | mstore (size : ByteSize) (ptr value : α)
  | mcopy (dst src length : α)
  | sstore (key value : α)
  | tstore (key value : α)
  | calldatacopy (dst offset length : α)
  | codecopy (dst offset length : α)
  | extcodecopy (account dst offset length : α)
  | returndatacopy (dst offset length : α)
  | log0 (offset length : α)
  | log1 (offset length topic0 : α)
  | log2 (offset length topic0 topic1 : α)
  | log3 (offset length topic0 topic1 topic2 : α)
  | log4 (offset length topic0 topic1 topic2 topic3 : α)
  | setImmutable (immutable : ImmutableId) (runtimePtr value : α)
  | noop

inductive Operation
  | «let» (out : VarId) (e : Expr VarId)
  | icall (function : FunctionId) (ins outs : Array VarId)
  | stmt (s : Stmt VarId)

/-- How a block ends. Block ids are local to the enclosing function. -/
inductive Control (α : Type)
  | iret
  | continuesTo (target : BlockId)
  | branches (condition : α) (nonZero zero : BlockId)
  | switch (condition : α) (cases : Array (Word × BlockId)) (fallback : Option BlockId)
  | stop
  | «return» (offset length : α)
  | revert (offset length : α)
  | invalid
  | selfdestruct (beneficiary : α)
  | icallNever (function : FunctionId) (ins : Array α)

section resolve
universe u
variable {m : Type → Type u} [Monad m]

def Expr.resolve (l : VarId → m Word) : Expr VarId → m (Expr Word)
  | .unop op a => do return .unop op (← l a)
  | .binop op a b => do return .binop op (← l a) (← l b)
  | .ternop op a b c => do return .ternop op (← l a) (← l b) (← l c)
  | .const v => pure (.const v)
  | .copy x => do return .copy (← l x)
  | .query q => pure (.query q)
  | .balance a => do return .balance (← l a)
  | .extcodehash a => do return .extcodehash (← l a)
  | .blockhash n => do return .blockhash (← l n)
  | .blobhash i => do return .blobhash (← l i)
  | .sload k => do return .sload (← l k)
  | .tload k => do return .tload (← l k)
  | .calldataload o => do return .calldataload (← l o)
  | .calldatasize => pure .calldatasize
  | .codesize => pure .codesize
  | .extcodesize a => do return .extcodesize (← l a)
  | .returndatasize => pure .returndatasize
  | .keccak256 o n => do return .keccak256 (← l o) (← l n)
  | .malloc n => do return .malloc (← l n)
  | .mallocany n => do return .mallocany (← l n)
  | .mload size p => do return .mload size (← l p)
  | .create v o n => do return .create (← l v) (← l o) (← l n)
  | .create2 v o n s => do return .create2 (← l v) (← l o) (← l n) (← l s)
  | .call g a v ao an ro rn =>
    do return .call (← l g) (← l a) (← l v) (← l ao) (← l an) (← l ro) (← l rn)
  | .callcode g a v ao an ro rn =>
    do return .callcode (← l g) (← l a) (← l v) (← l ao) (← l an) (← l ro) (← l rn)
  | .delegatecall g a ao an ro rn =>
    do return .delegatecall (← l g) (← l a) (← l ao) (← l an) (← l ro) (← l rn)
  | .staticcall g a ao an ro rn =>
    do return .staticcall (← l g) (← l a) (← l ao) (← l an) (← l ro) (← l rn)
  | .dataOffset d => pure (.dataOffset d)
  | .runtimeStartOffset => pure .runtimeStartOffset
  | .initEndOffset => pure .initEndOffset
  | .runtimeLength => pure .runtimeLength
  | .getImmutable i => pure (.getImmutable i)

def Stmt.resolve (l : VarId → m Word) : Stmt VarId → m (Stmt Word)
  | .mstore size p v => do return .mstore size (← l p) (← l v)
  | .mcopy d s n => do return .mcopy (← l d) (← l s) (← l n)
  | .sstore k v => do return .sstore (← l k) (← l v)
  | .tstore k v => do return .tstore (← l k) (← l v)
  | .calldatacopy d o n => do return .calldatacopy (← l d) (← l o) (← l n)
  | .codecopy d o n => do return .codecopy (← l d) (← l o) (← l n)
  | .extcodecopy a d o n => do return .extcodecopy (← l a) (← l d) (← l o) (← l n)
  | .returndatacopy d o n => do return .returndatacopy (← l d) (← l o) (← l n)
  | .log0 o n => do return .log0 (← l o) (← l n)
  | .log1 o n t0 => do return .log1 (← l o) (← l n) (← l t0)
  | .log2 o n t0 t1 => do return .log2 (← l o) (← l n) (← l t0) (← l t1)
  | .log3 o n t0 t1 t2 => do return .log3 (← l o) (← l n) (← l t0) (← l t1) (← l t2)
  | .log4 o n t0 t1 t2 t3 => do return .log4 (← l o) (← l n) (← l t0) (← l t1) (← l t2) (← l t3)
  | .setImmutable i p v => do return .setImmutable i (← l p) (← l v)
  | .noop => pure .noop

def Control.resolve (l : VarId → m Word) : Control VarId → m (Control Word)
  | .iret => pure .iret
  | .continuesTo t => pure (.continuesTo t)
  | .branches c nonZero zero => do return .branches (← l c) nonZero zero
  | .switch c cases fallback => do return .switch (← l c) cases fallback
  | .stop => pure .stop
  | .return o n => do return .return (← l o) (← l n)
  | .revert o n => do return .revert (← l o) (← l n)
  | .invalid => pure .invalid
  | .selfdestruct a => do return .selfdestruct (← l a)
  | .icallNever g ins => do return .icallNever g (← ins.mapM l)

end resolve

structure Block where
  inputs : Array VarId := #[]
  outputs : Array VarId := #[]
  ops : Array Operation := #[]
  control : Control VarId

inductive ReturnKind
  | never
  | values (count : Nat)

structure Function where
  entry : BlockId
  returns : ReturnKind
  blocks : Array Block

structure Program where
  init : FunctionId
  main : FunctionId
  functions : Array Function
  data : Array ByteArray := #[]
  mainDatas : List (Fin data.size)
  immutables : Array ByteSize := #[]

namespace Program

def ValidDataId (p : Program) : DataId → Prop := fun id => id.id < p.data.size

def ValidImmutableId (p : Program) : ImmutableId → Prop := fun id => id.id < p.immutables.size

end Program

inductive Entry
  | init
  | main
  deriving DecidableEq, Repr

instance : GetElem? Program ImmutableId ByteSize Program.ValidImmutableId where
  getElem p id valid := p.immutables[id.id]
  getElem? p id := p.immutables[id.id]?

instance : GetElem? Program DataId ByteArray Program.ValidDataId where
  getElem p id valid := p.data[id.id]
  getElem? p id := p.data[id.id]?


end Sir
