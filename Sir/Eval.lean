import ITree
import Std.Data.TreeMap
import Sir.Effect
import Sir.Layout
import Sir.Memory
import Host.Effect
import Host.Keccak
import Host.Interp

open Host

namespace Sir

abbrev Vars := Std.TreeMap VarId Word

namespace Vars

def lookup (l : Vars) (v : VarId) : SirM Word := do
  let some w := l[v]? | malformed "undefined var"
  return w

def lookupAll (l : Vars) (vs : Array VarId) : SirM (Array Word) := vs.mapM (lookup l)

def assignAll (l₀ : Vars) (vs : Array VarId) (ws : Array Word) : SirM Vars := do
  unless vs.size = ws.size do malformed "var assign arity mismatch"
  return (vs.zip ws).foldl (fun lᵢ (v, w) => lᵢ.insert v w) l₀

end Vars

structure Context where
  program : Program
  layout : Layout program
  mode : ExecutionMode
  env : Env
  immutables : Immutables program mode.kind

def Context.checkStateful (ctx : Context) : SirM Unit := do
  if ctx.mode.static then
    Host.halt .invalid

def Context.code (ctx : Context) : SirM ByteArray := do
  match hmode : ctx.mode with
  | .creation ctorData => return (ctx.layout.init ++ ctorData)
  | .call _ _ =>
    let imms := (hmode ▸ ctx.immutables).getMain
    let some code := ctx.layout.withSetImmutables imms | malformed "ill-formed immutables"
    return code

def mem.writeFromSlice (dst : Word) (src : ByteArray) (offset length : Word) : SirM Unit :=
  write dst (src.slicePadded offset.toNat length.toNat)

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

def Query.eval (env : Env) : Query → SirM Word
  | .gas => Host.gas
  | .selfbalance => Host.selfbalance
  | .address => pure env.address.toWord
  | .origin => pure env.origin.toWord
  | .caller => pure env.caller.toWord
  | .callvalue => pure env.callvalue
  | .gasprice => pure env.gasprice
  | .coinbase => pure env.coinbase.toWord
  | .timestamp => pure env.timestamp
  | .number => pure env.number
  | .prevrandao => pure env.prevrandao
  | .gaslimit => pure env.gaslimit
  | .chainid => pure env.chainid
  | .basefee => pure env.basefee
  | .blobbasefee => pure env.blobbasefee

def log (ctx : Context) (offset len : Word) (topics : Array Word) : SirM Unit := do
  ctx.checkStateful 
  Host.log (← mem.read offset len) topics

def execCall (ctx : Context) (ck : CallKind) (gas to inOff inLen outOff outLen : Word) : SirM Word := do
  match ck with
  | .call value => do unless value = 0 do ctx.checkStateful
  | .staticcall | .delegatecall => pure ()
  let input ← mem.read inOff inLen
  let succ : Bool ← Host.host <| .call ck gas (.ofWord to) input
  let retSize ← returndata.size
  let copiedOutLen := if retSize ≤ outLen then retSize else outLen
  mem.writeFromSlice outOff (← Host.returndata).val 0 copiedOutLen
  return .ofBool succ

def Context.getImmutable (ctx : Context) (id : ImmutableId) : SirM Word := do
  let imm_slots ← match heq : ctx.mode.kind with
    | .creation => malformed "getting immutable in init"
    | .call => pure (heq ▸ ctx.immutables).getMain.slots
  let some imm_size := ctx.program[id]?  | malformed  "invalid immutable id"
  let some v := imm_slots[id.id]? | malformed "missing immutable slot"
  unless v.HasSize imm_size do malformed "immutable value too large for slot"
  return v

def Context.getDataOffset (ctx : Context) (id : DataId) : SirM Word := do
  let i :=
    ← if hvalid : ctx.program.ValidDataId id
    then pure ⟨id.id, hvalid⟩
    else malformed "undefined data id"
  match ctx.mode.kind with
  | .creation => pure <| (.ofU32 ·.val) <| ctx.layout.initDataOffsets i
  | .call => do
    if hmd : i ∈ ctx.program.mainDatas then
      return (.ofU32 ·.val) <| ctx.layout.mainDataOffsets i hmd
    else malformed "data not defined in main"

def Expr.eval (ctx : Context) : Expr Word → SirM Word
  | .unop op a => pure (op.eval a)
  | .binop op a b => pure (op.eval a b)
  | .ternop op a b c => pure (op.eval a b c)
  | .const v => pure v
  | .copy x => pure x
  | .query q => q.eval ctx.env
  | .balance a => Host.balance (.ofWord a)
  | .extcodehash a => do
    if Address.ofWord a = ctx.env.address
    then return .keccak256 (← ctx.code)
    else Host.extcodehash (.ofWord a)
  | .blockhash n => pure (ctx.env.blockhash n)
  | .blobhash i => pure (ctx.env.blobhash i)
  | .sload k => Host.persistent.load k
  | .tload k => Host.transient.load k
  | .calldataload offset => ctx.mode.calldata.slicePadded offset.toNat 32 |> Word.ofBytes |> pure
  | .calldatasize => pure ctx.mode.calldata.size
  | .codesize => return (← ctx.code).size
  | .extcodesize a => do
    let code ← if Address.ofWord a = ctx.env.address
      then ctx.code
      else Host.extcode (.ofWord a)
    return code.size
  | .returndatasize => returndata.size
  | .keccak256 offset length => Word.keccak256 <$> mem.read offset length
  | .malloc size => alloc_zeroed size
  | .mallocany size => alloc_uninit size
  | .mload size ptr => Word.ofBytes <$> mem.read ptr (Word.ofNat size.toNat)
  | .create value offset length => do
      ctx.checkStateful
      let code ← mem.read offset length
      let a ← Host.create value code
      return a.toWord
  | .create2 value offset length salt => do
      ctx.checkStateful
      let code ← mem.read offset length
      let a ← Host.create2 value salt code
      return a.toWord
  | .call gas to value inOff inLen outOff outLen =>
      execCall ctx (.call value) gas to inOff inLen outOff outLen
  | .delegatecall gas to inOff inLen outOff outLen => do
      execCall ctx .delegatecall gas to inOff inLen outOff outLen
  | .staticcall gas to inOff inLen outOff outLen => do
      execCall ctx .staticcall gas to inOff inLen outOff outLen
  | .dataOffset d =>
    ctx.getDataOffset d
  | .mainStartOffset => do
      unless (ctx.mode.kind = .creation) do malformed "accessing main start outside of init"
      return .ofU32 ctx.layout.mainStartOffset.val
  | .mainLength => pure ctx.layout.main.size
  | .initEndOffset => do
      unless (ctx.mode.kind = .creation) do malformed "accessing init end offset outside of init"
      return ctx.layout.init.size
  | .getImmutable id => ctx.getImmutable id


def Stmt.exec (ctx : Context) : Stmt Word → SirM Unit
  | .mstore size ptr v => mem.write ptr (Word.toBytes size v)
  | .mcopy dst src length => mem.copy { dst, src, length }
  | .sstore k v => do ctx.checkStateful; persistent.store k v
  | .tstore k v => do ctx.checkStateful; transient.store k v
  | .calldatacopy dst offset length => mem.writeFromSlice dst ctx.mode.calldata offset length
  | .codecopy dst offset length => do mem.writeFromSlice dst (← ctx.code) offset length
  | .extcodecopy a dst offset length => do
      let code ← Host.extcode (.ofWord a)
      mem.writeFromSlice dst code offset length
  | .returndatacopy dst offset length => do
      unless (offset.toNat + length.toNat ≤ (← returndata.size))
        do Host.halt .invalid
      mem.writeFromSlice dst (← Host.returndata).val offset length
  | .log0 offset length => log ctx offset length #[]
  | .log1 offset length t0 => log ctx offset length #[t0]
  | .log2 offset length t0 t1 => log ctx offset length #[t0, t1]
  | .log3 offset length t0 t1 t2 => log ctx offset length #[t0, t1, t2]
  | .log4 offset length t0 t1 t2 t3 => log ctx offset length #[t0, t1, t2, t3]
  | .setImmutable id ptr v => do
      unless (ctx.mode.kind = .creation) do malformed "setting immutable outside of init"
      let i : Fin _ ←
        if h : ctx.program.ValidImmutableId id
        then pure ⟨id.id, h⟩
        else malformed "invalid immutable id"
      for ⟨offset, _⟩ in ctx.layout.immutableOffsets i do
        -- Unsure if overflow would already implicitly be UB here to making it explicit
        let slotPtr := ptr + Word.ofU32 offset
        unless (ptr ≤ slotPtr) do ub .illegalOverflow
        mem.write slotPtr (v.toBytes ctx.program.immutables[i])
  | .noop => pure ()

abbrev CallI := FunctionId × Array Word
abbrev CallO  := Array Word
abbrev CallE := Effect.Rec CallI CallO EvalE

def evalSwitch (cond : Word) (cases : Array (Word × BlockId)) (fallback : Option BlockId)
  : SirM BlockId := do
  for (value, dst) in cases do
    if value = cond then
      return dst
  let some fallback := fallback | ub .switchNoMatch
  return fallback

def evalFn (ctx : Context) : CallI → SirM CallO := CoFree.fix fun evalFn (fn, args) => do
  let .some fn := ctx.program[fn]? | malformed "undefined function"
  let mut inputs := args
  let mut bi := fn.entry
  let mut vars : Vars := ∅
  repeat
    let .some block := fn[bi]? | malformed "undefined block"
    vars ← vars.assignAll block.inputs inputs
    for op in block.ops do
      match ← liftM (op.resolve vars.lookup) with
      | .«let» out expr =>
          let value ← expr.eval ctx
          vars := vars.insert out value
      | .stmt s => s.exec ctx
      | .icall fn args outs =>
          let results ← evalFn (fn, args)
          vars ← vars.assignAll outs results
    let ctrl ← liftM (block.control.resolve vars.lookup)
    bi ← match ctrl with
      | .iret =>
        let .values count := fn.returns | malformed "iret from never function"
        let outs ← vars.lookupAll block.outputs
        unless count = outs.size do malformed "iret outs != return value count"
        return outs
      | .continuesTo dst => pure dst
      | .branches cond nonZero zero => pure (if cond ≠ 0 then nonZero else zero)
      | .switch cond cases fallback => evalSwitch cond cases fallback
      | .stop => Host.halt (.ret .empty)
      | .return offset length =>
          let data ← mem.read offset length
          Host.halt (.ret data)
      | .revert offset length =>
          let data ← mem.read offset length
          Host.halt (.revert data)
      | .invalid => Host.halt .invalid
      | .selfdestruct a =>
        ctx.checkStateful
        Host.halt (.selfdestruct (.ofWord a))
      | .icallNever fn args =>
          let _ ← evalFn (fn, args)
          malformed "icall never returned"
    inputs ← vars.lookupAll block.outputs

def runInner (ctx : Context) : SirM Empty := do
  let entryFn := match ctx.mode.kind with
    | .creation => ctx.program.init
    | .call => ctx.program.main
  let _ ← evalFn ctx (entryFn, #[])
  malformed "top-level entry point returned instead of terminating"

def Program.run
  (p : Program)
  (layout : Layout p)
  (mode : ExecutionMode)
  (env : Env)
  (imm : Immutables p mode.kind)
  (w₀ : World)
  : CoFree WorldE MemoryND (UB ⊕ Outcome) :=
    ⟨p, layout, mode, env, imm⟩
    |> runInner
    |> interpMem
    |> Host.interpHost env.address w₀

inductive InitOutcome
  | ret (imms : MainImmutables) (store : Store)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Address) (store : Store)

def Program.runInit
  (p : Program)
  (layout : Layout p)
  (ctorArgs : ByteArray)
  (env : Env)
  (w₀ : World)
  : CoFree WorldE MemoryND (UB ⊕ InitOutcome) :=
  p.run layout (.creation ctorArgs) env .init w₀
  |> Functor.map fun
    | .inr (.ret returnedMain s') => match layout.toMainImmutables returnedMain with
      | .some m => .inr (.ret m s')
      | .none => .inl .unsoundMain
    | .inr (.revert d) => .inr (.revert d)
    | .inr .invalid => .inr .invalid
    | .inr (.selfdestruct b s') => .inr (.selfdestruct b s')
    | .inl ub => .inl ub

def Program.runMain
  (p : Program)
  (layout : Layout p)
  (imms : MainImmutables)
  (static : Bool)
  (calldata : BytesX32)
  (env : Env)
  (w₀ : World)
  : CoFree WorldE MemoryND (UB ⊕ Outcome) :=
  p.run layout (.call static calldata) env (.main imms) w₀

def DefinedAnd {α : Type} (r : α → α → Prop) : UB ⊕ α → UB ⊕ α → Prop
  | .inl _ub, _ => False
  | _, .inl _ub => False
  | .inr a, .inr b => r a b

end Sir
