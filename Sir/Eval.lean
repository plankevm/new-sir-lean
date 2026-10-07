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

def query (q : Query) : CoFree EvalE Word := host (.query q)

def fault {α : Type} (f : Fault) : CoFree EvalE α := do
  let e ← host (.fault f)
  Empty.elim e

def malformed {α : Type} (m : Malformed) : CoFree EvalE α := fault (.malformed m)

def lookup (l : Locals) (v : VarId) : CoFree EvalE Word :=
  match l[v]? with
  | some w => pure w
  | none => malformed (.undefinedVariable v)

def lookupAll (l : Locals) (vs : Array VarId) : CoFree EvalE (List Word) :=
  vs.toList.mapM (lookup l)

def assignAll (l : Locals) (vs : Array VarId) (ws : List Word) : CoFree EvalE Locals :=
  if vs.size = ws.length then pure ((vs.toList.zip ws).foldl (fun l (v, w) => l.insert v w) l)
  else malformed (.arity vs.size ws.length)

def read (offset length : Word) : CoFree EvalE ByteArray :=
  mem (.read offset.toNat length.toNat)

def write (offset : Word) (bytes : ByteArray) : CoFree EvalE Unit :=
  mem (.write offset.toNat bytes)

def copyIn (src : ByteArray) (dst offset length : Word) : CoFree EvalE (List Word) := do
  write dst (src.slicePad offset.toNat length.toNat)
  pure []

def callOut (kind : CallKind) (gas account argsOff argsLen retOff retLen : Word) :
    CoFree EvalE (List Word) := do
  let input ← read argsOff argsLen
  let (ok, out) : Bool × ByteArray ← host (.call kind gas account input)
  mem (.setReturnData out)
  write retOff (out.extract 0 (min retLen.toNat out.size))
  pure [Word.ofBool ok]

def createOut (value off len : Word) (salt : Option Word) : CoFree EvalE (List Word) := do
  let initcode ← read off len
  let (account, out) : Word × ByteArray ← host (.create value salt initcode)
  mem (.setReturnData out)
  pure [account]

def logOut (off len : Word) (topics : List Word) : CoFree EvalE (List Word) := do
  host (.log topics (← read off len))
  pure []

def halt {α : Type} (op : HostOp) (h : HostOp.Resp op = Empty) : CoFree EvalE α := do
  let e ← host op
  Empty.elim (h ▸ e)

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

def execEvm : EvmOp → List Word → CoFree EvalE (List Word)
  | .keccak256, [off, len] => do pure [Word.keccak256 (← read off len)]
  | .address, [] => do pure [← query .address]
  | .balance, [a] => do pure [← query (.balance a)]
  | .origin, [] => do pure [← query .origin]
  | .caller, [] => do pure [← query .caller]
  | .callvalue, [] => do pure [← query .callvalue]
  | .calldataload, [off] => do pure [Word.ofBytes ((← host .calldata).slicePad off.toNat 32)]
  | .calldatasize, [] => do pure [BitVec.ofNat 256 (← host .calldata).size]
  | .calldatacopy, [dst, off, len] => do copyIn (← host .calldata) dst off len
  | .codesize, [] => do pure [BitVec.ofNat 256 (← host .code).size]
  | .codecopy, [dst, off, len] => do copyIn (← host .code) dst off len
  | .gasprice, [] => do pure [← query .gasprice]
  | .extcodesize, [a] => do pure [BitVec.ofNat 256 (← host (.extcode a)).size]
  | .extcodecopy, [a, dst, off, len] => do copyIn (← host (.extcode a)) dst off len
  | .returndatasize, [] => do pure [BitVec.ofNat 256 (← mem .returnData).size]
  | .returndatacopy, [dst, off, len] => do
    let data ← mem .returnData
    if off.toNat + len.toNat ≤ data.size then copyIn data dst off len
    else halt .invalid rfl
  | .extcodehash, [a] => do pure [← query (.extcodehash a)]
  | .gas, [] => do pure [← query .gas]
  | .blockhash, [n] => do pure [← query (.blockhash n)]
  | .coinbase, [] => do pure [← query .coinbase]
  | .timestamp, [] => do pure [← query .timestamp]
  | .number, [] => do pure [← query .number]
  | .difficulty, [] => do pure [← query .prevrandao]
  | .gaslimit, [] => do pure [← query .gaslimit]
  | .chainid, [] => do pure [← query .chainid]
  | .selfbalance, [] => do pure [← query .selfbalance]
  | .basefee, [] => do pure [← query .basefee]
  | .blobhash, [i] => do pure [← query (.blobhash i)]
  | .blobbasefee, [] => do pure [← query .blobbasefee]
  | .sload, [k] => do pure [← query (.sload k)]
  | .sstore, [k, v] => do host (.sstore k v); pure []
  | .tload, [k] => do pure [← query (.tload k)]
  | .tstore, [k, v] => do host (.tstore k v); pure []
  | .mcopy, [dst, src, len] => do mem (.copy dst.toNat src.toNat len.toNat); pure []
  | .log0, [off, len] => logOut off len []
  | .log1, [off, len, t0] => logOut off len [t0]
  | .log2, [off, len, t0, t1] => logOut off len [t0, t1]
  | .log3, [off, len, t0, t1, t2] => logOut off len [t0, t1, t2]
  | .log4, [off, len, t0, t1, t2, t3] => logOut off len [t0, t1, t2, t3]
  | .create, [v, off, len] => createOut v off len none
  | .create2, [v, off, len, salt] => createOut v off len (some salt)
  | .call, [g, a, v, ao, al, ro, rl] => callOut (.call v) g a ao al ro rl
  | .callcode, [g, a, v, ao, al, ro, rl] => callOut (.callcode v) g a ao al ro rl
  | .delegatecall, [g, a, ao, al, ro, rl] => callOut .delegatecall g a ao al ro rl
  | .staticcall, [g, a, ao, al, ro, rl] => callOut .staticcall g a ao al ro rl
  | op, args => malformed (.badOperands op args.length)

def execOp (ctx : Ctx) (call : CallI → CoFree EvalE (Array Word)) (l : Locals) :
    Operation → CoFree EvalE Locals
  | .unop op a out => do pure (l.insert out (op.eval (← lookup l a)))
  | .binop op a b out => do pure (l.insert out (op.eval (← lookup l a) (← lookup l b)))
  | .ternop op a b c out => do
    pure (l.insert out (op.eval (← lookup l a) (← lookup l b) (← lookup l c)))
  | .evm op ins outs => do assignAll l outs (← execEvm op (← lookupAll l ins))
  | .malloc size out => do pure (l.insert out (← mem (.alloc true (← lookup l size).toNat)))
  | .mallocany size out => do pure (l.insert out (← mem (.alloc false (← lookup l size).toNat)))
  | .mload size ptr out => do
    pure (l.insert out (Word.ofBytes (← mem (.read (← lookup l ptr).toNat size.val))))
  | .mstore size ptr value => do
    write (← lookup l ptr) (Word.toBytes size.val (← lookup l value))
    pure l
  | .copy src out => do pure (l.insert out (← lookup l src))
  | .const value out => pure (l.insert out value)
  | .dataOffset d out =>
    if d.id < ctx.program.data.size then pure (l.insert out (ctx.layout.dataOffset ctx.entry d))
    else malformed (.invalidData d)
  | .noop => pure l
  | .icall f ins outs => do
    let rs ← call (f, (← lookupAll l ins).toArray)
    assignAll l outs rs.toList
  | .runtimeStartOffset out =>
    if ctx.entry = .init then pure (l.insert out ctx.layout.runtimeStartOffset) else malformed .wrongEntry
  | .initEndOffset out =>
    if ctx.entry = .init then pure (l.insert out ctx.layout.initEndOffset) else malformed .wrongEntry
  | .runtimeLength out => pure (l.insert out ctx.layout.runtimeLength)
  | .getImmutable i out => do
    unless ctx.entry = .main do malformed .wrongEntry
    let some v := ctx.immutables.values[i.id]? | malformed (.invalidImmutable i)
    pure (l.insert out v)
  | .setImmutable i ptr value => do
    unless ctx.entry = .init do malformed .wrongEntry
    unless ctx.program.main.isSome do malformed .noMain
    let some size := ctx.program.immutables[i.id]? | malformed (.invalidImmutable i)
    let p ← lookup l ptr
    let bytes := Word.toBytes size.val (← lookup l value)
    for r in ctx.layout.immutableRefs i do
      mem (.write (p.toNat + r) bytes)
    pure l

def block (f : FunctionId) (fn : Function) (b : BlockId) : CoFree EvalE Block :=
  match fn.blocks[b.id]? with
  | some blk => pure blk
  | none => malformed (.invalidBlock f b)

/-- Control transfer within `fn`: the source block's outputs become the target block's inputs. -/
def jump (f : FunctionId) (fn : Function) (l : Locals) (src : Block) (target : BlockId) :
    CoFree EvalE (IterStep (BlockId × Locals) (Array Word)) := do
  let dst ← block f fn target
  let l ← assignAll l dst.inputs (← lookupAll l src.outputs)
  pure (.repeat (target, l))

def evalFunction (ctx : Ctx) : CallI → CoFree SirE (Array Word) :=
  CoFree.fix fun call (f, args) => do
    let some fn := ctx.program.functions[f.id]? | malformed (.invalidFunction f)
    let l ← assignAll ∅ (← block f fn fn.entry).inputs args.toList
    CoFree.iter (fn.entry, l) fun (b, l) => do
      let blk ← block f fn b
      let mut l := l
      for op in blk.ops do
        l ← execOp ctx call l op
      match blk.control with
      | .iret => match fn.returns with
        | .never => malformed (.returnKindMismatch f)
        | .values n => do
          let rs ← lookupAll l blk.outputs
          if rs.length = n then pure (.exit rs.toArray) else malformed (.returnKindMismatch f)
      | .continuesTo t => jump f fn l blk t
      | .branches c nonZero zero => do
        jump f fn l blk (if (← lookup l c) ≠ 0 then nonZero else zero)
      | .switch c cases fallback => do
        let v ← lookup l c
        match cases.find? (·.1 == v), fallback with
        | some (_, t), _ => jump f fn l blk t
        | none, some t => jump f fn l blk t
        | none, none => fault (.ub .switchNoMatch)
      | .stop => halt .stop rfl
      | .return off len => do halt (.ret (← read (← lookup l off) (← lookup l len))) rfl
      | .revert off len => do halt (.revert (← read (← lookup l off) (← lookup l len))) rfl
      | .invalid => halt .invalid rfl
      | .selfdestruct a => do halt (.selfdestruct (← lookup l a)) rfl
      | .icallNever g ins => do
        let _ ← call (g, (← lookupAll l ins).toArray)
        malformed (.neverReturned g)

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
  | some f => (evalFunction ⟨p, layout, e, imm⟩ (f, #[])).bind fun _ => malformedTop .entryReturned

end Sir
