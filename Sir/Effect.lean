import Host
import ITree.Effect
import ITree.Machine
import Sir.Ir


namespace Sir

open CoFree

inductive UB
  | malformed (reason : String)
  | switchNoMatch
  | illegalOverflow
  | memoryOutOfBounds (offset length : Nat)
  | uninitializedRead (offset length : Nat)
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

end Sir
