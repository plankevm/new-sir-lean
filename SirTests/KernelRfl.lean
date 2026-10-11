import Lean

open Lean Elab Tactic Meta

/-- Closes `lhs = rhs` by `rfl` checked by the kernel alone, as `decide +kernel` does. Unlike
`decide`, the goal may mention local variables, as long as reduction never inspects them (the
elaborator's reduction gives up on such goals much earlier than the kernel's). -/
elab "kernel_rfl" : tactic => liftMetaFinishingTactic fun g => g.withContext do
  let type ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := type.eq? | throwError "kernel_rfl: goal is not an equation"
  let xs := (← getLCtx).getFVars.filter fun x => type.containsFVar x.fvarId!
  let lemmaType ← mkForallFVars xs type
  let pf ← mkLambdaFVars xs (← mkEqRefl lhs)
  let levels := (collectLevelParams {} lemmaType).params.toList
  let name ← withOptions (Elab.async.set · false) (mkAuxLemma levels lemmaType pf)
  g.assign (mkAppN (mkConst name (levels.map .param)) xs)
