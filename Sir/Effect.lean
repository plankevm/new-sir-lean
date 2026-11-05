import ITree.Effect
import ITree.Machine
import Sir.Ir


namespace Sir

open CoFree

inductive UB
  | malformed (reason : String)
  | switchNoMatch
  | illegalOverflow
  | memoryOutOfBounds (offset : Word) (length : Nat)
  | outOfMemory (size : Word)
  deriving DecidableEq, Repr

structure MemCopy where
  dst : Word
  src : Word
  length : Word

inductive AllocKind | zeroed | uninitialized

inductive SirOp
  | alloc (kind : AllocKind) (size : Word)
  | read (offset length : Word)
  | write (offset : Word) (bytes : ByteArray)
  | copy (copy : MemCopy)
  | ub (ub : UB)

def SirOp.Resp : SirOp → Type
  | .alloc .. => Word
  | .read .. => ByteArray
  | .write .. => Unit
  | .copy .. => Unit
  | .ub _ => Empty

abbrev SirE : Effect := ⟨SirOp, SirOp.Resp⟩
abbrev EvalE := Host.HostE ⊕ₑ SirE
abbrev SirM (α : Type) : Type 1 := CoFree EvalE .none α

private def sir_op (op : SirE.Op) : SirM (SirE.Resp op) := CoFree.perform (E := EvalE) (Sum.inr op)
def alloc_zeroed (size : Word) := sir_op (.alloc .zeroed size)
def alloc_uninit (size : Word) := sir_op (.alloc .uninitialized size)
def mem.read (offset len : Word) := sir_op (.read offset len)
def mem.write (offset : Word) (bytes : ByteArray) := sir_op (.write offset bytes)
def mem.copy (copy : MemCopy)  := sir_op (.copy copy)
def ub {α : Type} (ub : UB) : SirM α := do nomatch ← sir_op (.ub ub)
def malformed {α : Type} (reason : String) := ub (α := α) <| .malformed reason
def returndata.size : SirM Word := (·.size) <$> Host.returndata

end Sir
