import Sir.Ir
import Lean

/-! `sir! { ... }`: plankc's SIR text format (`plankc/sir/docs/ir_text_format.md`) as a term of
type `Program`.

```
data greeting 0x48656c6c6f
immutable owner 20
fn init:
    entry a b -> s {
        s = add a b
        r = icall @callee s 1
        => r ? @done : @fail
    }
    done { stop }
    fail { revert 0 0 }
fn callee -> 1:
    entry x y -> z {
        z = sub x y
        iret
    }
```

Deviations from plankc, all forced by the Lean IR or by Lean's lexer:
* Statements are separated by newlines (or `;`) and must start in the same column, as in a
  tactic block; a block's lines and a function's blocks are indented past their header.
* A function returns values only if its header says how many: `fn f -> 2:`. Without `-> n` it is
  `.never`, which plankc instead infers from the call sites.
* The first block of a function is its entry; `init` and `main` are the entry points, and both
  are required.
* Every data segment is also part of main's code (`mainDatas`).
* A number operand is, as in plankc, a fresh local set by a `const` just before the operation.
  `(t)` is a number operand computed by the Lean term `t`.
* Locals are numbered by first occurrence within their function, skipping the ids written
  explicitly as `$n` (plankc's printed form); `@n` names a block or function by its index.
* `difficulty` is accepted for `prevrandao`; `callcode` is not supported. -/

namespace Sir.Syntax

open Lean

declare_syntax_cat sir_local
syntax ident : sir_local
syntax (name := localNum) "$" noWs num : sir_local

declare_syntax_cat sir_param
syntax sir_local : sir_param
syntax num : sir_param
syntax "(" term ")" : sir_param
syntax (name := labelName) "@" noWs ident : sir_param
syntax (name := labelNum) "@" noWs num : sir_param
syntax (name := dataRef) "." noWs ident : sir_param
syntax (name := immutableRef) "%" noWs ident : sir_param

-- Words that are keywords only in SIR are non-reserved (`&"..."`), so they stay identifiers in
-- Lean; `behavior` makes their categories try them where an identifier starts.
declare_syntax_cat sir_case (behavior := symbol)
syntax num " => " sir_param : sir_case
syntax &"default" " => " sir_param : sir_case

declare_syntax_cat sir_line (behavior := both)
-- `colGt` stops a line at the next one, which starts in the line's own column.
syntax (name := opLine) (atomic(sir_local (colGt sir_local)* " = "))? (ident <|> "return")
  (colGt sir_param)* : sir_line
syntax (name := jumpLine) "=>" sir_param : sir_line
syntax (name := branchLine) "=>" sir_local " ? " sir_param " : " sir_param : sir_line
syntax (name := switchLine) &"switch" sir_local " {" sir_case* "}" : sir_line

declare_syntax_cat sir_block
syntax ident sir_local* (" -> " sir_local*)? " {" sepByIndentSemicolon(sir_line) "}" : sir_block

declare_syntax_cat sir_item (behavior := symbol)
syntax (name := fnItem) withPosition(&"fn" ident (" -> " num)? ":" (colGt sir_block)+) : sir_item
syntax (name := dataItem) &"data" ident num : sir_item
syntax (name := immutableItem) &"immutable" ident num : sir_item

syntax (name := sirProgram) "sir!" " {" sir_item* "}" : term

/-- Names of the program's functions, data segments and immutables, and of the current
function's blocks, each mapped to its index. -/
structure Scope where
  functions : List (String × Nat)
  data : List (String × Nat)
  immutables : List (String × Nat)
  blocks : List (String × Nat) := []

/-- The current function's locals, and the operations setting number operands of the line
being expanded. -/
structure Locals where
  names : List (String × Nat) := []
  explicit : List Nat
  next : Nat := 0
  pre : Array Term := #[]

abbrev M := ReaderT Scope (StateT Locals MacroM)

def lookup (what : String) (map : List (String × Nat)) (x : Ident) : MacroM Nat :=
  match map.lookup x.getId.toString with
  | some i => pure i
  | none => Macro.throwErrorAt x s!"unknown {what} {x.getId}"

def fresh : M Nat := do
  let s ← get
  let mut n := s.next
  while s.explicit.contains n do n := n + 1
  set { s with next := n + 1 }
  pure n

def localId (x : TSyntax `sir_local) : M Nat := do
  if x.raw.isOfKind ``localNum then return x.raw[1].isNatLit?.getD 0
  let name := x.raw[0].getId.toString
  if let some i := (← get).names.lookup name then return i
  let i ← fresh
  modify fun s => { s with names := (name, i) :: s.names }
  pure i

def var (n : Nat) : Term := Syntax.mkCApp ``VarId.mk #[quote n]

/-- The Lean term of a word written as a `num` or as `(t)`, if `p` is one. -/
def word? (p : TSyntax `sir_param) : MacroM (Option Term) :=
  match p with
  | `(sir_param| $n:num) => some <$> `(($n : Word))
  | `(sir_param| ($t)) => some <$> `(($t : Word))
  | _ => pure none

def operand (p : TSyntax `sir_param) : M Term := do
  if let some w ← word? p then
    let i ← fresh
    let op ← `(Operation.let $(var i) (Expr.const $w))
    modify fun s => { s with pre := s.pre.push op }
    return var i
  match p with
  | `(sir_param| $x:sir_local) => return var (← localId x)
  | _ => Macro.throwErrorAt p "expected a local or a number"

def label (map : List (String × Nat)) (what : String) (p : TSyntax `sir_param) : MacroM Nat :=
  if p.raw.isOfKind ``labelName then lookup what map ⟨p.raw[1]⟩
  else if p.raw.isOfKind ``labelNum then pure (p.raw[1].isNatLit?.getD 0)
  else Macro.throwErrorAt p s!"expected @{what}"

def ref (kind : SyntaxNodeKind) (map : List (String × Nat)) (what : String)
    (p : TSyntax `sir_param) : MacroM Term :=
  if p.raw.isOfKind kind then do return quote (← lookup what map ⟨p.raw[1]⟩)
  else Macro.throwErrorAt p s!"expected a reference to a {what}"

def unops : List (String × Name) :=
  [("iszero", ``UnOp.iszero), ("not", ``UnOp.not), ("clz", ``UnOp.clz)]

def binops : List (String × Name) :=
  [("add", ``BinOp.add), ("mul", ``BinOp.mul), ("sub", ``BinOp.sub), ("div", ``BinOp.div),
   ("sdiv", ``BinOp.sdiv), ("mod", ``BinOp.mod), ("smod", ``BinOp.smod), ("exp", ``BinOp.exp),
   ("signextend", ``BinOp.signextend), ("lt", ``BinOp.lt), ("gt", ``BinOp.gt),
   ("slt", ``BinOp.slt), ("sgt", ``BinOp.sgt), ("eq", ``BinOp.eq), ("and", ``BinOp.and),
   ("or", ``BinOp.or), ("xor", ``BinOp.xor), ("byte", ``BinOp.byte), ("shl", ``BinOp.shl),
   ("shr", ``BinOp.shr), ("sar", ``BinOp.sar)]

def ternops : List (String × Name) := [("addmod", ``TernOp.addmod), ("mulmod", ``TernOp.mulmod)]

def queries : List (String × Name) :=
  [("address", ``Query.address), ("origin", ``Query.origin), ("caller", ``Query.caller),
   ("callvalue", ``Query.callvalue), ("gasprice", ``Query.gasprice), ("gas", ``Query.gas),
   ("coinbase", ``Query.coinbase), ("timestamp", ``Query.timestamp),
   ("number", ``Query.number), ("prevrandao", ``Query.prevrandao),
   ("difficulty", ``Query.prevrandao), ("gaslimit", ``Query.gaslimit),
   ("chainid", ``Query.chainid), ("selfbalance", ``Query.selfbalance),
   ("basefee", ``Query.basefee), ("blobbasefee", ``Query.blobbasefee)]

/-- `Expr` constructors whose arguments are all operands, with their arity. -/
def exprs : List (String × Name × Nat) :=
  [("copy", ``Expr.copy, 1), ("balance", ``Expr.balance, 1),
   ("extcodehash", ``Expr.extcodehash, 1), ("blockhash", ``Expr.blockhash, 1),
   ("blobhash", ``Expr.blobhash, 1), ("sload", ``Expr.sload, 1), ("tload", ``Expr.tload, 1),
   ("calldataload", ``Expr.calldataload, 1), ("calldatasize", ``Expr.calldatasize, 0),
   ("codesize", ``Expr.codesize, 0), ("extcodesize", ``Expr.extcodesize, 1),
   ("returndatasize", ``Expr.returndatasize, 0), ("keccak256", ``Expr.keccak256, 2),
   ("malloc", ``Expr.malloc, 1), ("mallocany", ``Expr.mallocany, 1),
   ("create", ``Expr.create, 3), ("create2", ``Expr.create2, 4), ("call", ``Expr.call, 7),
   ("delegatecall", ``Expr.delegatecall, 6),
   ("staticcall", ``Expr.staticcall, 6), ("runtime_start_offset", ``Expr.mainStartOffset, 0),
   ("init_end_offset", ``Expr.initEndOffset, 0), ("runtime_length", ``Expr.mainLength, 0)] ++
  unops.map (fun (s, n) => (s, n, 1)) ++ binops.map (fun (s, n) => (s, n, 2)) ++
  ternops.map (fun (s, n) => (s, n, 3)) ++ queries.map (fun (s, n) => (s, n, 0))

def stmts : List (String × Name × Nat) :=
  [("mcopy", ``Stmt.mcopy, 3), ("sstore", ``Stmt.sstore, 2), ("tstore", ``Stmt.tstore, 2),
   ("calldatacopy", ``Stmt.calldatacopy, 3), ("codecopy", ``Stmt.codecopy, 3),
   ("extcodecopy", ``Stmt.extcodecopy, 4), ("returndatacopy", ``Stmt.returndatacopy, 3),
   ("log0", ``Stmt.log0, 2), ("log1", ``Stmt.log1, 3), ("log2", ``Stmt.log2, 4),
   ("log3", ``Stmt.log3, 5), ("log4", ``Stmt.log4, 6), ("noop", ``Stmt.noop, 0)]

def controls : List (String × Name × Nat) :=
  [("iret", ``Control.iret, 0), ("stop", ``Control.stop, 0), ("return", ``Control.return, 2),
   ("revert", ``Control.revert, 2), ("invalid", ``Control.invalid, 0),
   ("selfdestruct", ``Control.selfdestruct, 1)]

/-- Constructor `c` applied first to `args`, then to the operands `ps`. -/
def apply (c : Name) (args : Array Term) (ps : Array (TSyntax `sir_param)) : M Term := do
  pure (Syntax.mkCApp c (args ++ (← ps.mapM operand)))

/-- The byte size of `mload<bits>`/`mstore<bits>`. -/
def memSize (ref : Syntax) (bits : String) : MacroM Term := do
  let some b := bits.toNat? | Macro.throwErrorAt ref "expected mload<bits> or mstore<bits>"
  unless b % 8 = 0 ∧ 8 ≤ b ∧ b ≤ 256 do
    Macro.throwErrorAt ref "memory access size must be 8 to 256 bits, a multiple of 8"
  `((⟨$(quote (b / 8)), by decide⟩ : ByteSize))

/-- An operation, or a block's control. -/
inductive Line
  | op (t : Term)
  | control (t : Term)

def expandOp (outs : Array (TSyntax `sir_local)) (m : Syntax) (ps : Array (TSyntax `sir_param)) :
    M Line := do
  let scope ← read
  let name := if m.isIdent then m.getId.toString else ((m.find? (·.isAtom)).map (·.getAtomVal)).getD ""
  let arity (n : Nat) : MacroM Unit := unless ps.size = n do
    Macro.throwErrorAt m s!"{name} takes {n} operands, got {ps.size}"
  let outputs (n : Nat) : MacroM Unit := unless outs.size = n do
    Macro.throwErrorAt m s!"{name} defines {n} locals, got {outs.size}"
  -- Outputs first, so that locals are numbered in the order they are written.
  let outIds ← outs.mapM localId
  let expr (e : Term) : M Line := do
    let #[out] := outIds | Macro.throwErrorAt m s!"{name} defines 1 local, got {outs.size}"
    return .op (← `(Operation.let $(var out) $e))
  let stmt (s : Term) : M Line := do outputs 0; return .op (← `(Operation.stmt $s))
  let first : MacroM (TSyntax `sir_param) := match ps[0]? with
    | some p => pure p
    | none => Macro.throwErrorAt m s!"{name} needs an operand"
  if name = "const" ∨ name = "large_const" then
    arity 1
    let p ← first
    let some w ← word? p | Macro.throwErrorAt p "expected a number"
    return ← expr (← `(Expr.const $w))
  if name = "data_offset" then
    arity 1
    return ← expr (Syntax.mkCApp ``Expr.dataOffset #[← ref ``dataRef scope.data "data" (← first)])
  if name = "getimmutable" then
    arity 1
    return ← expr (Syntax.mkCApp ``Expr.getImmutable
      #[← ref ``immutableRef scope.immutables "immutable" (← first)])
  if name = "setimmutable" then
    arity 3
    return ← stmt (← apply ``Stmt.setImmutable
      #[← ref ``immutableRef scope.immutables "immutable" (← first)] ps[1:])
  if name = "icall" ∨ name = "icall_never" then
    let some f := ps[0]? | Macro.throwErrorAt m s!"{name} needs a function"
    let f ← label scope.functions "function" f
    let ins ← ps[1:].toArray.mapM operand
    if name = "icall_never" then
      outputs 0
      return .control (← `(Control.icallNever $(quote f) #[$ins,*]))
    return .op (← `(Operation.icall $(quote f) #[$ins,*] #[$(outIds.map var),*]))
  if let some bits := name.dropPrefix? "mload" then
    arity 1; return ← expr (← apply ``Expr.mload #[← memSize m bits.toString] ps)
  if let some bits := name.dropPrefix? "mstore" then
    arity 2; return ← stmt (← apply ``Stmt.mstore #[← memSize m bits.toString] ps)
  if let some (c, n) := exprs.lookup name then
    arity n
    if let some u := unops.lookup name then return ← expr (← apply ``Expr.unop #[mkCIdent u] ps)
    if let some b := binops.lookup name then return ← expr (← apply ``Expr.binop #[mkCIdent b] ps)
    if let some t := ternops.lookup name then
      return ← expr (← apply ``Expr.ternop #[mkCIdent t] ps)
    if let some q := queries.lookup name then return ← expr (Syntax.mkCApp ``Expr.query #[mkCIdent q])
    return ← expr (← apply c #[] ps)
  if let some (c, n) := stmts.lookup name then
    arity n; return ← stmt (← apply c #[] ps)
  if let some (c, n) := controls.lookup name then
    arity n; outputs 0; return .control (← apply c #[] ps)
  Macro.throwErrorAt m s!"unknown operation {name}"

def line (l : TSyntax `sir_line) : M Line := do
  let blocks := (← read).blocks
  match l with
  | `(sir_line| => $c:sir_local ? $nz : $z) =>
    let c ← localId c
    return .control (← `(Control.branches $(var c) $(quote (← label blocks "block" nz))
      $(quote (← label blocks "block" z))))
  | `(sir_line| => $t) => return .control (← `(Control.continuesTo $(quote (← label blocks "block" t))))
  | `(sir_line| switch $c { $cases* }) =>
    let c ← localId c
    let mut arms : Array Term := #[]
    let mut fallback ← `(none)
    for case in cases do
      match case with
      | `(sir_case| $n:num => $t) =>
        arms := arms.push (← `((($n : Word), ($(quote (← label blocks "block" t)) : BlockId))))
      | `(sir_case| default => $t) => fallback ← `(some $(quote (← label blocks "block" t)))
      | _ => Macro.throwUnsupported
    return .control (← `(Control.switch $(var c) #[$arms,*] $fallback))
  | _ =>
    let outs := if l.raw[0].isNone then #[] else #[l.raw[0][0]] ++ l.raw[0][1].getArgs
    expandOp (outs.map (⟨·⟩)) l.raw[1] (l.raw[2].getArgs.map (⟨·⟩))

def block (b : TSyntax `sir_block) : M Term := do
  let ins ← b.raw[1].getArgs.mapM fun i => return var (← localId ⟨i⟩)
  let outs ← (if b.raw[2].isNone then #[] else b.raw[2][1].getArgs).mapM fun o =>
    return var (← localId ⟨o⟩)
  let lines : Array (TSyntax `sir_line) := b.raw[4].getSepArgs.map (⟨·⟩)
  let mut ops : Array Term := #[]
  let mut control : Option Term := none
  for l in lines do
    if control.isSome then Macro.throwErrorAt l "nothing may follow a block's control"
    modify fun s => { s with pre := #[] }
    let r ← line l
    ops := ops ++ (← get).pre
    match r with
    | .op t => ops := ops.push t
    | .control t => control := some t
  let some ctl := control | Macro.throwErrorAt b "a block must end in control flow or a halt"
  `(({ inputs := #[$ins,*], outputs := #[$outs,*], ops := #[$ops,*], control := $ctl } : Block))

/-- The ids written as `$n` anywhere in `stx`. -/
def explicitIds : Syntax → List Nat
  | stx@(.node _ k args) =>
    if k == ``localNum then [stx[1].isNatLit?.getD 0]
    else (args.attach.map fun ⟨a, _⟩ => explicitIds a).toList.flatten
  | _ => []

def function (scope : Scope) (stx : Syntax) : MacroM Term := do
  let `(sir_item| fn $_:ident $[-> $n:num]? : $blocks*) := stx | Macro.throwUnsupported
  let names := blocks.toList.zipIdx.map fun (b, i) => (b.raw[0].getId.toString, i)
  let (blocks, _) ← (blocks.mapM block) { scope with blocks := names } |>.run
    { explicit := explicitIds stx }
  let returns ← match n with
    | some n => `(ReturnKind.values $n)
    | none => `(ReturnKind.never)
  `(({ entry := 0, returns := $returns, blocks := #[$blocks,*] } : Function))

/-- The bytes of a hex literal, keeping its leading zeros. -/
def bytes (n : TSyntax `num) : MacroM Term := do
  let some s := n.raw.isLit? numLitKind | Macro.throwUnsupported
  let some hex := s.dropPrefix? "0x" | Macro.throwErrorAt n "expected a hex literal"
  let digits := hex.toString.toList
  unless digits.length % 2 = 0 do Macro.throwErrorAt n "expected whole bytes"
  let rec pairs : List Char → List Term
    | a :: b :: rest => Syntax.mkNumLit s!"0x{a}{b}" :: pairs rest
    | _ => []
  `(ByteArray.mk #[$((pairs digits).toArray),*])

macro_rules
  | `(sir! { $items* }) => do
    let named (k : SyntaxNodeKind) :=
      (items.filter (·.raw.isOfKind k)).toList.zipIdx.map fun (i, n) => (i.raw[1].getId.toString, n)
    let scope : Scope :=
      { functions := named ``fnItem, data := named ``dataItem, immutables := named ``immutableItem }
    let fns ← (items.filter (·.raw.isOfKind ``fnItem)).mapM fun i => function scope i.raw
    let segments ← (items.filter (·.raw.isOfKind ``dataItem)).mapM fun i => bytes ⟨i.raw[2]⟩
    let imms ← (items.filter (·.raw.isOfKind ``immutableItem)).mapM fun i =>
      `((⟨$(⟨i.raw[2]⟩), by decide⟩ : ByteSize))
    let some init := scope.functions.lookup "init" | Macro.throwError "no function `init`"
    let some main := scope.functions.lookup "main" | Macro.throwError "no function `main`"
    `(({ init := $(quote init), main := $(quote main), functions := #[$fns,*],
         data := #[$segments,*], mainDatas := List.finRange _,
         immutables := #[$imms,*] } : Program))

end Sir.Syntax
