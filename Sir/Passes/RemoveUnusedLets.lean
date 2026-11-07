import Sir.WellFormed

namespace Sir

def Expr.isRemovable {α : Type} : Expr α → Bool
  | .query .gas | .create .. | .create2 .. | .call .. | .delegatecall .. | .staticcall .. => false
  | _ => true

def Operation.removableLet? : Operation VarId → Option (VarId × List VarId)
  | .let out e => if e.isRemovable then some (out, e.reads) else none
  | _ => none

def Operation.isDeadLet (dead : Array Bool) (op : Operation VarId) : Bool :=
  match op.removableLet? with
  | some (out, _) => dead[out.id]? == some true
  | none => false

namespace RemoveUnusedLets

def countUses (n : Nat) (ops : Array (Operation VarId)) (blocks : Array Block) : Array Nat := Id.run do
  let mut uses := Array.replicate n 0
  for op in ops do
    for u in op.reads do
      uses := uses.modify u.id (· + 1)
  for b in blocks do
    for u in b.control.reads ++ b.outputs.toList do
      uses := uses.modify u.id (· + 1)
  return uses

def collectDefs (n : Nat) (ops : Array (Operation VarId)) : Array (List (List VarId)) := Id.run do
  let mut defs := Array.replicate n []
  for op in ops do
    if let some (out, reads) := op.removableLet? then
      defs := defs.modify out.id (reads :: ·)
  return defs

def release (readss : List (List VarId)) (uses : Array Nat) (work : Array Nat) :
    Array Nat × Array Nat := Id.run do
  let mut uses := uses
  let mut work := work
  for reads in readss do
    for u in reads do
      uses := uses.modify u.id (· - 1)
      if uses[u.id]? = some 0 then
        work := work.push u.id
  return (uses, work)

end RemoveUnusedLets

open RemoveUnusedLets in
def Function.deadVars (fn : Function) : Array Bool := Id.run do
  let ops := fn.blocks.flatMap (·.ops)
  let mut n := 0
  for op in ops do
    if let some (out, _) := op.removableLet? then
      n := max n (out.id + 1)
  let defs := collectDefs n ops
  let mut uses := countUses n ops fn.blocks
  let mut dead := Array.replicate n false
  let mut work := #[]
  for v in [0:n] do
    if uses[v]? = some 0 then
      work := work.push v
  for _ in [0:n] do
    let some v := work.back? | break
    work := work.pop
    if dead[v]? = some false ∧ uses[v]? = some 0 then
      dead := dead.setIfInBounds v true
      if let some readss := defs[v]? then
        (uses, work) := release readss uses work
  return dead

def Function.removeUnusedLets (fn : Function) : Function :=
  let dead := fn.deadVars
  { fn with blocks := fn.blocks.map fun b => { b with ops := b.ops.filter (!·.isDeadLet dead) } }

def Program.removeUnusedLets (p : Program) : Program :=
  { p with functions := p.functions.map Function.removeUnusedLets }

end Sir
