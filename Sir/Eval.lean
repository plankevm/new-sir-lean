import Std.Data.HashMap
import Sir.Effect
import Sir.Keccak

/-! The evaluator: one `CoFree` program per entry point. It owns only control and locals;
internal calls are `CoFree.fix` frames and blocks are `CoFree.iter` iterations. -/

namespace Sir

open CoFree (perform)

abbrev CallI := FunctionId × Array Word
abbrev EvalE := Effect.Rec CallI (Array Word) SirE
abbrev Locals := Std.HashMap VarId Word

structure Ctx where
  program : Program
  layout : Layout
  entry : Entry
  immutables : Immutables program

def mem (op : MemOp) : CoFree EvalE (MemOp.Resp op) := perform (E := EvalE) (.inr (.inl op))

def host (op : HostOp) : CoFree EvalE (HostOp.Resp op) := perform (E := EvalE) (.inr (.inr op))

def fault {α : Type} (f : Fault) : CoFree EvalE α := do
  let e ← host (.fault f)
  Empty.elim e

def malformed {α : Type} (m : Malformed) : CoFree EvalE α := fault (.malformed m)

def halt {α : Type} (op : HostOp) (h : HostOp.Resp op = Empty := by rfl) : CoFree EvalE α := do
  let e ← host op
  Empty.elim (h ▸ e)

def lookup (l : Locals) (v : VarId) : CoFree EvalE Word :=
  match l[v]? with
  | some w => pure w
  | none => malformed (.undefinedVariable v)

def lookupAll (l : Locals) (vs : Array VarId) : CoFree EvalE (Array Word) :=
  vs.mapM (lookup l)

def assignAll (l : Locals) (vs : Array VarId) (ws : Array Word) : CoFree EvalE Locals :=
  if vs.size = ws.size then pure ((vs.zip ws).foldl (fun l (v, w) => l.insert v w) l)
  else malformed (.arity vs.size ws.size)

def Ctx.requireEntry (ctx : Ctx) (e : Entry) : CoFree EvalE Unit :=
  unless ctx.entry = e do malformed .wrongEntry

def read (offset length : Word) : CoFree EvalE ByteArray :=
  mem (.read offset.toNat length.toNat)

def write (offset : Word) (bytes : ByteArray) : CoFree EvalE Unit :=
  mem (.write offset.toNat bytes)

def lengthOf (b : ByteArray) : Word := BitVec.ofNat 256 b.size

def copyIn (src : ByteArray) (dst offset length : Word) : CoFree EvalE Unit :=
  write dst (src.slicePad offset.toNat length.toNat)

def externalCall (kind : CallKind) (gas account argsOffset argsLength retOffset retLength : Word) :
    CoFree EvalE Word := do
  let input ← read argsOffset argsLength
  let (ok, out) : Bool × ByteArray ← host (.call kind gas account input)
  mem (.setReturnData out)
  write retOffset (out.extract 0 (min retLength.toNat out.size))
  pure (Word.ofBool ok)

def createContract (value offset length : Word) (salt : Option Word) : CoFree EvalE Word := do
  let input ← read offset length
  let (account, out) : Word × ByteArray ← host (.create value salt input)
  mem (.setReturnData out)
  pure account

def log (offset length : Word) (topics : Array Word) : CoFree EvalE Unit := do
  let data ← read offset length
  host (.log topics data)

def UnOp.eval : UnOp → Word → Word
  | .iszero, a => Word.iszero a
  | .not, a => ~~~a
  | .clz, a => Word.clz a

def BinOp.eval : BinOp → Word → Word → Word
  | .add, a, b => a + b
  | .mul, a, b => a * b
  | .sub, a, b => a - b
  | .div, a, b => Word.div a b
  | .sdiv, a, b => Word.sdiv a b
  | .mod, a, b => Word.mod a b
  | .smod, a, b => Word.smod a b
  | .exp, a, b => Word.exp a b
  | .signextend, b, x => Word.signextend b x
  | .lt, a, b => Word.lt a b
  | .gt, a, b => Word.gt a b
  | .slt, a, b => Word.slt a b
  | .sgt, a, b => Word.sgt a b
  | .eq, a, b => Word.eq a b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .byte, i, x => Word.byte i x
  | .shl, s, x => Word.shl s x
  | .shr, s, x => Word.shr s x
  | .sar, s, x => Word.sar s x

def TernOp.eval : TernOp → Word → Word → Word → Word
  | .addmod, a, b, n => Word.addmod a b n
  | .mulmod, a, b, n => Word.mulmod a b n

def Expr.eval (ctx : Ctx) : Expr Word → CoFree EvalE Word
  | .unop op a => pure (op.eval a)
  | .binop op a b => pure (op.eval a b)
  | .ternop op a b c => pure (op.eval a b c)
  | .const v => pure v
  | .copy x => pure x
  | .query q => host (.query q)
  | .balance a => host (.balance a)
  | .extcodehash a => host (.extcodehash a)
  | .blockhash n => host (.blockhash n)
  | .blobhash i => host (.blobhash i)
  | .sload k => host (.sload k)
  | .tload k => host (.tload k)
  | .calldataload offset => do
    let data ← host .calldata
    pure (Word.ofBytes (data.slicePad offset.toNat 32))
  | .calldatasize => do
    let data ← host .calldata
    pure (lengthOf data)
  | .codesize => do
    let code ← host .code
    pure (lengthOf code)
  | .extcodesize a => do
    let code ← host (.extcode a)
    pure (lengthOf code)
  | .returndatasize => do
    let data ← mem .returnData
    pure (lengthOf data)
  | .keccak256 offset length => do
    let data ← read offset length
    pure (Word.keccak256 data)
  | .malloc size => mem (.alloc true size.toNat)
  | .mallocany size => mem (.alloc false size.toNat)
  | .mload size ptr => do
    let bytes ← mem (.read ptr.toNat size.val)
    pure (Word.ofBytes bytes)
  | .create v offset length => createContract v offset length none
  | .create2 v offset length salt => createContract v offset length (some salt)
  | .call g a v ao an ro rn => externalCall (.call v) g a ao an ro rn
  | .callcode g a v ao an ro rn => externalCall (.callcode v) g a ao an ro rn
  | .delegatecall g a ao an ro rn => externalCall .delegatecall g a ao an ro rn
  | .staticcall g a ao an ro rn => externalCall .staticcall g a ao an ro rn
  | .dataOffset d =>
    if d.id < ctx.program.data.size then pure (ctx.layout.dataOffset ctx.entry d)
    else malformed (.invalidData d)
  | .runtimeStartOffset => do ctx.requireEntry .init; pure ctx.layout.runtimeStartOffset
  | .initEndOffset => do ctx.requireEntry .init; pure ctx.layout.initEndOffset
  | .runtimeLength => pure ctx.layout.runtimeLength
  | .getImmutable i => do
    ctx.requireEntry .main
    let some v := ctx.immutables[i]? | malformed (.invalidImmutable i)
    pure v

def Stmt.exec (ctx : Ctx) : Stmt Word → CoFree EvalE Unit
  | .mstore size ptr v => write ptr (Word.toBytes size.val v)
  | .mcopy dst src length => mem (.copy dst.toNat src.toNat length.toNat)
  | .sstore k v => host (.sstore k v)
  | .tstore k v => host (.tstore k v)
  | .calldatacopy dst offset length => do
    let data ← host .calldata
    copyIn data dst offset length
  | .codecopy dst offset length => do
    let code ← host .code
    copyIn code dst offset length
  | .extcodecopy a dst offset length => do
    let code ← host (.extcode a)
    copyIn code dst offset length
  | .returndatacopy dst offset length => do
    let data ← mem .returnData
    unless offset.toNat + length.toNat ≤ data.size do halt .invalid
    copyIn data dst offset length
  | .log0 offset length => log offset length #[]
  | .log1 offset length t0 => log offset length #[t0]
  | .log2 offset length t0 t1 => log offset length #[t0, t1]
  | .log3 offset length t0 t1 t2 => log offset length #[t0, t1, t2]
  | .log4 offset length t0 t1 t2 t3 => log offset length #[t0, t1, t2, t3]
  | .setImmutable i ptr v => do
    ctx.requireEntry .init
    unless ctx.program.main.isSome do malformed .noMain
    let some size := ctx.program.immutables[i.id]? | malformed (.invalidImmutable i)
    for r in ctx.layout.immutableRefs i do
      mem (.write (ptr.toNat + r) (Word.toBytes size.val v))
  | .noop => pure ()

abbrev Call := FunctionId → Array Word → CoFree EvalE (Array Word)

def execOp (ctx : Ctx) (call : Call) (l : Locals) : Operation → CoFree EvalE Locals
  | .«let» x e => do
    let e ← e.resolve (lookup l)
    let w ← e.eval ctx
    pure (l.insert x w)
  | .icall f ins outs => do
    let args ← lookupAll l ins
    let results ← call f args
    assignAll l outs results
  | .stmt s => do
    let s ← s.resolve (lookup l)
    s.exec ctx
    pure l

def block (f : FunctionId) (fn : Function) (b : BlockId) : CoFree EvalE Block :=
  match fn.blocks[b.id]? with
  | some blk => pure blk
  | none => malformed (.invalidBlock f b)

/-- Control transfer within `fn`: the source block's outputs become the target block's inputs. -/
def jumpTo (f : FunctionId) (fn : Function) (l : Locals) (src : Block) (target : BlockId) :
    CoFree EvalE (IterStep (BlockId × Locals) (Array Word)) := do
  let dst ← block f fn target
  let values ← lookupAll l src.outputs
  let l ← assignAll l dst.inputs values
  pure (.repeat (target, l))

def execControl (call : Call) (f : FunctionId) (fn : Function) (l : Locals) (blk : Block) :
    CoFree EvalE (IterStep (BlockId × Locals) (Array Word)) := do
  let jump := jumpTo f fn l blk
  let control ← blk.control.resolve (lookup l)
  match control with
  | .iret => match fn.returns with
    | .never => malformed (.returnKindMismatch f)
    | .values n => do
      let rs ← lookupAll l blk.outputs
      if rs.size = n then pure (.exit rs) else malformed (.returnKindMismatch f)
  | .continuesTo t => jump t
  | .branches c nonZero zero => jump (if c ≠ 0 then nonZero else zero)
  | .switch c cases fallback =>
    match (cases.find? (·.1 == c)).map (·.2) <|> fallback with
    | some t => jump t
    | none => fault (.ub .switchNoMatch)
  | .stop => halt .stop
  | .return offset length => do
    let data ← read offset length
    halt (.ret data)
  | .revert offset length => do
    let data ← read offset length
    halt (.revert data)
  | .invalid => halt .invalid
  | .selfdestruct a => halt (.selfdestruct a)
  | .icallNever g args => do
    let _ ← call g args
    malformed (.neverReturned g)

def evalFunction (ctx : Ctx) : CallI → CoFree SirE (Array Word) :=
  CoFree.fix fun callI (f, args) => do
    let call : Call := fun g args => callI (g, args)
    let some fn := ctx.program.functions[f.id]? | malformed (.invalidFunction f)
    let entry ← block f fn fn.entry
    let l ← assignAll ∅ entry.inputs args
    CoFree.iter (fn.entry, l) fun (b, l) => do
      let blk ← block f fn b
      let mut l := l
      for op in blk.ops do
        l ← execOp ctx call l op
      execControl call f fn l blk

def malformedTop {α : Type} (m : Malformed) : CoFree SirE α := do
  let e ← perform (E := SirE) (.inr (.fault (.malformed m)))
  Empty.elim e

/-- An entry point runs until a halting control; entry functions take no inputs and
must not return. -/
def runEntry (p : Program) (layout : Layout) (imm : Immutables p) (e : Entry) :
    CoFree SirE Empty :=
  let f? := match e with
    | .init => some p.init
    | .main => p.main
  match f? with
  | none => malformedTop .noMain
  | some f =>
    (evalFunction ⟨p, layout, e, imm⟩ (f, #[])).bind fun _ => malformedTop (.neverReturned f)

end Sir
