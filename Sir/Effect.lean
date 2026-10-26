import Host
import Sir.Ir

/-! The effects of a SIR run.

The evaluator reads `Env` and emits `SirE = Mem ⊕ₑ HostE`. `Env` holds what stays fixed for
the whole frame, so reading it is pure: equivalence can ignore, reorder or drop those reads. `Mem`
(allocation, byte reads/writes, the return data buffer) is frame-local and handled by
`Sir.Memory`, which places each allocation by a branch (`Choice.placement`). `HostE` is the
shared EVM host interface (`Host.Effect`); `Host.interpStore` then makes storage and the world
concrete, leaving `Exec`: gas, logs, calls, creations and the end of the frame. -/

namespace Sir

open Host

inductive MemOp
  | alloc (zeroed : Bool) (size : Nat)
  | read (offset length : Nat)
  | write (offset : Nat) (bytes : ByteArray)
  | copy (dst src length : Nat)
  | returnData
  | setReturnData (bytes : ByteArray)

def MemOp.Resp : MemOp → Type
  | .alloc .. => Word
  | .read .. => ByteArray
  | .write .. => Unit
  | .copy .. => Unit
  | .returnData => ByteArray
  | .setReturnData _ => Unit

abbrev Mem : Effect := { Op := MemOp, Resp := MemOp.Resp }

abbrev SirE : Effect := Mem ⊕ₑ HostE

/-- What a run emits once `Mem`, storage and the world are handled. -/
abbrev Exec : Effect := WorldE

end Sir
