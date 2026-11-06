import Sir.Ir

namespace Sir

def Operation.isNoop {α : Type} : Operation α → Bool
  | .stmt .noop => true
  | _ => false

def Block.removeNoops (b : Block) : Block :=
  { b with ops := b.ops.filter fun op => !op.isNoop }

def Function.removeNoops (fn : Function) : Function :=
  { fn with blocks := fn.blocks.map Block.removeNoops }

def Program.removeNoops (p : Program) : Program :=
  { p with functions := p.functions.map Function.removeNoops }

end Sir
