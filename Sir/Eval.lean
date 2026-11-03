import ITree
import Std.Data.TreeMap
import Sir.Effect
import Sir.Layout
import Host.Effect
import Host.Keccak

open Host

namespace Sir

abbrev EvalE := HostE ⊕ₑ SirE
abbrev SirM (α : Type) : Type 1 := CoFree EvalE .none α

abbrev Vars := Std.TreeMap VarId Word

private def sir_op (op : SirE.Op) : SirM (SirE.Resp op) := CoFree.perform (E := EvalE) (Sum.inr op)
def alloc_zeroed (size : Word) := sir_op (.alloc true size)
def alloc_uninit (size : Word) := sir_op (.alloc false size)
def mem.read (offset len : Word) := sir_op (.read offset len)
def mem.write (offset : Word) (bytes : ByteArray) := sir_op (.write offset bytes)
def mem.copy (copy : MemCopy)  := sir_op (.copy copy)
def ub {α : Type} (ub : UB) : SirM α := do nomatch ← sir_op (.ub ub)
def malformed {α : Type} (reason : String) := ub (α := α) <| .malformed reason
def returndata : SirM ByteArray := do Host.returndata (N := .none)
def returndata.size : SirM Word := (·.size) <$> returndata

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
  env : Env
  immutables : Immutables program env.mode.kind

def Context.checkStateful (ctx : Context) : SirM Unit :=
  unless ctx.env.static do Host.halt (N := .none) .invalid

def Context.code (ctx : Context) : ByteArray := match hmode : ctx.env.mode with
  | .creation ctorData => ctx.layout.init ++ ctorData
  | .call a b =>
      let imms := ctx.immutables
      have h_eq : ctx.env.mode.kind = .call := by simp [ExecutionMode.kind, hmode]
      let immMain := (h_eq ▸ imms).getMain
      ctx.layout.withSetImmutables immMain ++ immMain.tail

def mem.writeFromSlice (dst : Word) (src : ByteArray) (offset length : Word) : SirM Unit :=
  write dst (src.slicePad offset.toNat length.toNat)

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
  | .gas => Host.gas (N := .none)
  | .selfbalance => Host.selfbalance (N := .none)
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
  Host.log (N := .none) (← mem.read offset len) topics

def execCall (ctx : Context) (ck : CallKind) (gas to inOff inLen outOff outLen : Word) : SirM Word := do
  match ck with
  | .call value => do unless value = 0 do ctx.checkStateful
  | .staticcall | .delegatecall => pure ()
  let input ← mem.read inOff inLen
  let succ : Bool ← Host.host (N := .none) <| .call ck gas (.ofWord to) input
  let retSize ← returndata.size
  let copiedOutLen := if retSize ≤ outLen then retSize else outLen
  mem.writeFromSlice outOff (← returndata) 0 copiedOutLen
  return .ofBool succ

def Expr.eval (ctx : Context) : Expr Word → SirM Word
  | .unop op a => pure (op.eval a)
  | .binop op a b => pure (op.eval a b)
  | .ternop op a b c => pure (op.eval a b c)
  | .const v => pure v
  | .copy x => pure x
  | .query q => q.eval ctx.env
  | .balance a => Host.balance (N := .none) (.ofWord a)
  | .extcodehash a => Host.extcodehash (N := .none) (.ofWord a)
  | .blockhash n => pure (ctx.env.blockhash n)
  | .blobhash i => pure (ctx.env.blobhash i)
  | .sload k => Host.persistent.load (N := .none) k
  | .tload k => Host.transient.load (N := .none) k
  | .calldataload offset => ctx.env.calldata.slicePad offset.toNat 32 |> Word.ofBytes |> pure
  | .calldatasize => pure ctx.env.calldata.size
  | .codesize => pure ctx.code.size
  | .extcodesize a => (·.size) <$> Host.extcode (N := .none) (.ofWord a)
  | .returndatasize => returndata.size
  | .keccak256 offset length => Word.keccak256 <$> mem.read offset length
  | .malloc size => alloc_zeroed size
  | .mallocany size => alloc_uninit size
  | .mload size ptr => Word.ofBytes <$> mem.read ptr (Word.ofNat size.toNat)
  | .create value offset length => do
      ctx.checkStateful
      let code ← mem.read offset length
      let a ← Host.create (N := .none) value code
      return a.toWord
  | .create2 value offset length salt => do
      ctx.checkStateful
      let code ← mem.read offset length
      let a ← Host.create2 (N := .none) value salt code
      return a.toWord
  | .call gas to value inOff inLen outOff outLen =>
      execCall ctx (.call value) gas to inOff inLen outOff outLen
  | .delegatecall gas to inOff inLen outOff outLen => do
      execCall ctx .delegatecall gas to inOff inLen outOff outLen
  | .staticcall gas to inOff inLen outOff outLen => do
      execCall ctx .staticcall gas to inOff inLen outOff outLen
  | .dataOffset d => do
      let i :=
        ← if hvalid : ctx.program.ValidDataId d
        then pure ⟨d.id, hvalid⟩
        else malformed "undefined data id"
      match henv : ctx.env.mode with
      | .creation _ => pure <| (.ofU32 ·.val) <| ctx.layout.initDataOffsets i
      | .call _ _ => do
          if hmd : i ∈ ctx.program.mainDatas then
            return (.ofU32 ·.val) <| ctx.layout.mainDataOffsets i hmd
          else malformed "data not defined in main"
  | .mainStartOffset => do
      unless (ctx.env.mode.kind = .creation) do malformed "accessing main start outside of init"
      return .ofU32 ctx.layout.mainStartOffset.val
  | .mainLength => pure ctx.layout.main.size
  | .initEndOffset => do
      unless (ctx.env.mode.kind = .creation) do malformed "accessing init end offset outside of init"
      return ctx.layout.init.size
  | .getImmutable id => do
      let henv : { p : Bool × ByteArray // ctx.env.mode = .call p.1 p.2 }
        ← match henv : ctx.env.mode with
        | .creation _ => malformed "getting immutable in init"
        | .call a b => pure ⟨(a, b), henv⟩
      let i : Fin ctx.program.immutables.size
        ← if hvalid : id.id < ctx.program.immutables.size
        then pure ⟨id.id, hvalid⟩
        else malformed "invalid immutable id"
      let imms := ctx.immutables
      have heq : ctx.env.mode.kind = .call := by simp [ExecutionMode.kind, henv.property]
      return (heq ▸ imms).getMain.slots[i]


def Stmt.exec (ctx : Context) : Stmt Word → SirM Unit
  | .mstore size ptr v => mem.write ptr (Word.toBytes size v)
  | .mcopy dst src length => mem.copy { dst, src, length }
  | .sstore k v => do ctx.checkStateful; persistent.store (N := .none) k v
  | .tstore k v => do ctx.checkStateful; transient.store (N := .none) k v
  | .calldatacopy dst offset length => mem.writeFromSlice dst ctx.env.calldata offset length
  | .codecopy dst offset length => mem.writeFromSlice dst ctx.code offset length
  | .extcodecopy a dst offset length => do
      let code ← Host.extcode (N := .none) (.ofWord a)
      mem.writeFromSlice dst code offset length
  | .returndatacopy dst offset length => do
      unless (offset.toNat + length.toNat ≤ (← returndata.size))
        do Host.halt (N := .none) .invalid
      mem.writeFromSlice dst (← returndata) offset length
  | .log0 offset length => log ctx offset length #[]
  | .log1 offset length t0 => log ctx offset length #[t0]
  | .log2 offset length t0 t1 => log ctx offset length #[t0, t1]
  | .log3 offset length t0 t1 t2 => log ctx offset length #[t0, t1, t2]
  | .log4 offset length t0 t1 t2 t3 => log ctx offset length #[t0, t1, t2, t3]
  | .setImmutable id ptr v => do
      unless (ctx.env.mode.kind = .creation) do malformed "setting immutable outside of init"
      let i : Fin _ ←
        if h : ctx.program.ValidImmutableId id
        then pure ⟨id.id, h⟩
        else malformed "invalid immutable id"
      unless v.HasSize ctx.program.immutables[i] do malformed "immutable value too large for slot"
      for ⟨offset, _⟩ in ctx.layout.immutableOffsets i do
        -- Unsure if overflow UB here to making it explicit
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
      | .iret => return ← vars.lookupAll block.outputs
      | .continuesTo dst => pure dst
      | .branches cond nonZero zero => pure (if cond ≠ 0 then nonZero else zero)
      | .switch cond cases fallback => evalSwitch cond cases fallback
      | .stop => Host.halt (N := .none) (.ret .empty)
      | .return offset length => do
          let data ← mem.read offset length
          Host.halt (N := .none) (.ret data)
      | .revert offset length => do
          let data ← mem.read offset length
          Host.halt (N := .none) (.revert data)
      | .invalid => Host.halt (N := .none) .invalid
      | .selfdestruct a => Host.halt (N := .none) (.selfdestruct (.ofWord a))
      | .icallNever fn args => do
          let _ ← evalFn (fn, args)
          malformed "icall never returned"
    inputs ← vars.lookupAll block.outputs


def run (p : Program) (layout : Layout p) (env : Env) (imm : Immutables p env.mode.kind) : SirM Empty := do
  let ctx := ⟨p, layout, env, imm⟩
  let entryFn := p[env.mode.kind]
  let _ ← evalFn ctx (entryFn, #[])
  malformed "top-level entry point returned instead of terminating"

end Sir
