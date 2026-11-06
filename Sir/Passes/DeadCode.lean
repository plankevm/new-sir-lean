import Sir.WellFormed

namespace Sir

namespace DeadCode

def reach (n : Nat) (roots : List Nat) (succs : Nat → List Nat) : Array Bool := Id.run do
  let mut seen := Array.replicate n false
  let mut work : Array Nat := #[]
  for r in roots do
    if seen[r]? = some false then
      seen := seen.setIfInBounds r true
      work := work.push r
  for _ in [0:n] do
    let some i := work.back? | break
    work := work.pop
    for j in succs i do
      if seen[j]? = some false then
        seen := seen.setIfInBounds j true
        work := work.push j
  return seen

def renumber (live : Array Bool) : Array (Option Nat) := Id.run do
  let mut ids := #[]
  let mut next := 0
  for l in live do
    if l then
      ids := ids.push (some next)
      next := next + 1
    else
      ids := ids.push none
  return ids

def rename (ids : Array (Option Nat)) (i : Nat) : Nat :=
  match ids[i]? with
  | some (some j) => j
  | _ => ids.size

end DeadCode

variable {α : Type}

def Operation.rename (fnMap : FunctionId → FunctionId) : Operation α → Operation α
  | .let out e => .let out e
  | .icall g ins outs => .icall (fnMap g) ins outs
  | .stmt s => .stmt s

def Control.rename (blockMap : BlockId → BlockId) (fnMap : FunctionId → FunctionId) :
    Control α → Control α
  | .iret => .iret
  | .continuesTo t => .continuesTo (blockMap t)
  | .branches c nonZero zero => .branches c (blockMap nonZero) (blockMap zero)
  | .switch c cases fallback =>
    .switch c (cases.map fun (v, t) => (v, blockMap t)) (fallback.map blockMap)
  | .stop => .stop
  | .return o n => .return o n
  | .revert o n => .revert o n
  | .invalid => .invalid
  | .selfdestruct a => .selfdestruct a
  | .icallNever g ins => .icallNever (fnMap g) ins

def Block.rename (blockMap : BlockId → BlockId) (fnMap : FunctionId → FunctionId) (b : Block) :
    Block :=
  { b with
    ops := b.ops.map (·.rename fnMap)
    control := b.control.rename blockMap fnMap }

namespace Function

def liveBlocks (fn : Function) : Array Bool :=
  DeadCode.reach fn.blocks.size [fn.entry.id] fun i =>
    match fn.blocks[i]? with
    | some b => b.control.targets.map (·.id)
    | none => []

def liveCallees (fn : Function) : List Nat := Id.run do
  let live := fn.liveBlocks
  let mut callees := #[]
  for (b, i) in fn.blocks.zipIdx do
    if live[i]? = some true then
      for op in b.ops do
        if let some g := op.callee? then
          callees := callees.push g.id
      if let some g := b.control.callee? then
        callees := callees.push g.id
  return callees.toList

def sweep (fnMap : FunctionId → FunctionId) (fn : Function) : Function := Id.run do
  let live := fn.liveBlocks
  let ids := DeadCode.renumber live
  let blockMap (b : BlockId) : BlockId := ⟨DeadCode.rename ids b.id⟩
  let mut blocks := #[]
  for (b, i) in fn.blocks.zipIdx do
    if live[i]? = some true then
      blocks := blocks.push (b.rename blockMap fnMap)
  return { entry := blockMap fn.entry, returns := fn.returns, blocks }

end Function

namespace Program

def liveFunctions (p : Program) : Array Bool :=
  DeadCode.reach p.functions.size [p.init.id, p.main.id] fun i =>
    match p.functions[i]? with
    | some fn => fn.liveCallees
    | none => []

def removeDeadCode (p : Program) : Program :=
  let live := p.liveFunctions
  let ids := DeadCode.renumber live
  let fnMap (f : FunctionId) : FunctionId := ⟨DeadCode.rename ids f.id⟩
  let functions := Id.run do
    let mut functions := #[]
    for (fn, i) in p.functions.zipIdx do
      if live[i]? = some true then
        functions := functions.push (fn.sweep fnMap)
    return functions
  { p with init := fnMap p.init, main := fnMap p.main, functions }

end Program

end Sir
