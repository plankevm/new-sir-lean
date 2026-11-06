import Sir.Ir

open Host

namespace Sir

variable {α : Type}

def Expr.reads : Expr VarId → List VarId
  | .unop _ a => [a]
  | .binop _ a b => [a, b]
  | .ternop _ a b c => [a, b, c]
  | .const _ | .query _ | .calldatasize | .codesize | .returndatasize => []
  | .copy a | .balance a | .extcodehash a | .blockhash a | .blobhash a | .sload a | .tload a
  | .calldataload a | .extcodesize a | .malloc a | .mallocany a | .mload _ a => [a]
  | .keccak256 o n => [o, n]
  | .create v o n => [v, o, n]
  | .create2 v o n s => [v, o, n, s]
  | .call g a v ao an ro rn => [g, a, v, ao, an, ro, rn]
  | .delegatecall g a ao an ro rn | .staticcall g a ao an ro rn => [g, a, ao, an, ro, rn]
  | .dataOffset _ | .mainStartOffset | .mainLength | .initEndOffset | .getImmutable _ => []

def Stmt.reads : Stmt VarId → List VarId
  | .mstore _ p v => [p, v]
  | .sstore k v | .tstore k v => [k, v]
  | .mcopy d s n | .calldatacopy d s n | .codecopy d s n | .returndatacopy d s n => [d, s, n]
  | .extcodecopy a d o n => [a, d, o, n]
  | .log0 o n => [o, n]
  | .log1 o n t0 => [o, n, t0]
  | .log2 o n t0 t1 => [o, n, t0, t1]
  | .log3 o n t0 t1 t2 => [o, n, t0, t1, t2]
  | .log4 o n t0 t1 t2 t3 => [o, n, t0, t1, t2, t3]
  | .setImmutable _ p v => [p, v]
  | .noop => []

def Operation.reads : Operation VarId → List VarId
  | .let _ e => e.reads
  | .icall _ ins _ => ins.toList
  | .stmt s => s.reads

def Operation.defs : Operation VarId → List VarId
  | .let out _ => [out]
  | .icall _ _ outs => outs.toList
  | .stmt _ => []

def Control.reads : Control VarId → List VarId
  | .branches c .. | .switch c .. | .selfdestruct c => [c]
  | .return o n | .revert o n => [o, n]
  | .icallNever _ ins => ins.toList
  | .iret | .continuesTo _ | .stop | .invalid => []

def Control.targets : Control α → List BlockId
  | .continuesTo t => [t]
  | .branches _ nonZero zero => [nonZero, zero]
  | .switch _ cases fallback => cases.toList.map (·.2) ++ fallback.toList
  | _ => []

def Block.defs (b : Block) : List VarId :=
  b.inputs.toList ++ b.ops.toList.flatMap Operation.defs

def Block.definedBefore (b : Block) (i : Nat) : List VarId :=
  b.inputs.toList ++ (b.ops.toList.take i).flatMap Operation.defs

def Block.DefinedBeforeUse (b : Block) (pre : List VarId) : Prop :=
  (∀ i (h : i < b.ops.size), ∀ v ∈ b.ops[i].reads, v ∈ pre ++ b.definedBefore i) ∧
    ∀ v ∈ b.control.reads ++ b.outputs.toList, v ∈ pre ++ b.definedBefore b.ops.size

instance (b : Block) (pre : List VarId) : Decidable (b.DefinedBeforeUse pre) := by
  unfold Block.DefinedBeforeUse; infer_instance

namespace Function

def defs (fn : Function) : List VarId :=
  fn.blocks.toList.flatMap Block.defs

inductive PathTo (fn : Function) : List Block → BlockId → Prop
  | entry : fn.PathTo [] fn.entry
  | step {prev b blk t} : fn.PathTo prev b → fn[b]? = some blk → t ∈ blk.control.targets →
      fn.PathTo (prev ++ [blk]) t

structure WF (fn : Function) : Prop where
  entry_valid : fn.ValidBlockId fn.entry
  ssa : fn.defs.Nodup
  definedBeforeUse : ∀ prev b blk, fn.PathTo prev b → fn[b]? = some blk →
    blk.DefinedBeforeUse (prev.flatMap Block.defs)
  validTargets : ∀ b ∈ fn.blocks, ∀ t ∈ b.control.targets,
    ∃ tb, fn[t]? = some tb ∧ tb.inputs.size = b.outputs.size
  iretArity : ∀ b ∈ fn.blocks, b.control = .iret → fn.returns = .values b.outputs.size

end Function

namespace Program

def Callee (p : Program) (g : FunctionId) (inputs : Nat) (returns : ReturnKind) : Prop :=
  ∃ fn, p[g]? = some fn ∧ fn.returns = returns ∧
    ∃ entry, fn[fn.entry]? = some entry ∧ entry.inputs.size = inputs

end Program

def Operation.ValidCall (p : Program) : Operation α → Prop
  | .icall g ins outs => p.Callee g ins.size (.values outs.size)
  | _ => True

def Control.ValidCall (p : Program) : Control α → Prop
  | .icallNever g ins => p.Callee g ins.size .never
  | _ => True

def Operation.callee? : Operation α → Option FunctionId
  | .icall g .. => some g
  | _ => none

def Control.callee? : Control α → Option FunctionId
  | .icallNever g _ => some g
  | _ => none

def Block.Calls (b : Block) (g : FunctionId) : Prop :=
  (∃ op ∈ b.ops, op.callee? = some g) ∨ b.control.callee? = some g

def Expr.ValidIn (p : Program) : ExecutionModeKind → Expr α → Prop
  | .creation, .dataOffset d => p.ValidDataId d
  | .call, .dataOffset d => ∃ h : p.ValidDataId d, ⟨d.id, h⟩ ∈ p.mainDatas
  | .creation, .getImmutable _ => False
  | .call, .getImmutable i => p.ValidImmutableId i
  | .call, .mainStartOffset | .call, .initEndOffset => False
  | _, _ => True

def Stmt.ValidIn (p : Program) : ExecutionModeKind → Stmt α → Prop
  | .creation, .setImmutable i .. => p.ValidImmutableId i
  | .call, .setImmutable .. => False
  | _, _ => True

def Operation.ValidIn (p : Program) (k : ExecutionModeKind) : Operation α → Prop
  | .let _ e => e.ValidIn p k
  | .stmt s => s.ValidIn p k
  | .icall .. => True

namespace Program

def CallEdge (p : Program) (caller callee : FunctionId) : Prop :=
  ∃ fn, p[caller]? = some fn ∧ ∃ prev b blk, fn.PathTo prev b ∧ fn[b]? = some blk ∧ blk.Calls callee

inductive Reachable (p : Program) (root : FunctionId) : FunctionId → Prop
  | root : p.Reachable root root
  | call {f g} : p.Reachable root f → p.CallEdge f g → p.Reachable root g

def ValidFrom (p : Program) (k : ExecutionModeKind) (root : FunctionId) : Prop :=
  ∀ f fn, p.Reachable root f → p[f]? = some fn →
    ∀ prev b blk, fn.PathTo prev b → fn[b]? = some blk → ∀ op ∈ blk.ops, op.ValidIn p k

structure WF (p : Program) : Prop where
  functions : ∀ fn ∈ p.functions, fn.WF
  validCalls : ∀ fn ∈ p.functions, ∀ b ∈ fn.blocks,
    (∀ op ∈ b.ops, op.ValidCall p) ∧ b.control.ValidCall p
  initEntry : p.Callee p.init 0 .never
  mainEntry : p.Callee p.main 0 .never
  initOps : p.ValidFrom .creation p.init
  mainOps : p.ValidFrom .call p.main
  /-- Simplifies stack code generation as the EVM stack can be utilized as the call stack -/
  acyclicCalls : ∀ f, ¬Relation.TransGen p.CallEdge f f

end Program

end Sir
