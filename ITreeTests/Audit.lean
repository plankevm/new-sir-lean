import Lean
import ITree

namespace ITreeTests.Audit

open Lean Elab Command

/-- Fails unless every library theorem uses only `propext`, `Quot.sound` and
`Classical.choice`. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let roots := [`CoFree, `Step, `Effect, `NonDeterminism]
  let mut bad : Array (Name × Name) := #[]
  let mut checked := 0
  for (name, info) in env.constants.toList do
    unless roots.contains name.getRoot do continue
    unless (env.getModuleIdxFor? name).any fun idx =>
        (env.header.moduleNames[idx.toNat]!).getRoot == `ITree do continue
    unless info matches .thmInfo _ do continue
    checked := checked + 1
    for ax in ← liftCoreM (collectAxioms name) do
      unless allowed.contains ax do bad := bad.push (name, ax)
  unless bad.isEmpty do throwError m!"disallowed axioms: {bad}"
  logInfo m!"axiom audit: {checked} theorems use only propext, Quot.sound, Classical.choice"

#audit_axioms

/-- The head constant of a theorem's proof term, under its binders. -/
private def proofHead : Expr → Option Name
  | .lam _ _ b _ => proofHead b
  | .mdata _ e => proofHead e
  | e => e.getAppFn.constName?

/-- Fails unless the library keeps definitions, proofs and theorem statements apart:
- a module `ITree.X` (definitions) declares no theorems (Prop-valued structure fields aside);
- a module `ITree.X.Proofs` may declare anything;
- a module `ITree.X.Theorems` declares only theorems whose proof is a `Proofs` theorem of
  the same name applied to arguments (instances may be named differently). -/
elab "#audit_layout" : command => do
  let env ← getEnv
  let mut bad : Array MessageData := #[]
  let mut stated : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.getRoot == `ITree && mod != `ITree do continue
    unless (← liftCoreM (findDeclarationRanges? name)).isSome do continue
    if env.isProjectionFn name then continue
    match mod.getString!, info with
    | "Proofs", _ => pure ()
    | "Theorems", .thmInfo val =>
      stated := stated + 1
      match proofHead val.value with
      | some head =>
        unless head.components.contains `Proofs do
          bad := bad.push m!"{name} ({mod}): proof is not a `Proofs` theorem"
        unless Meta.isInstanceCore env name || head.getString! == name.getString! do
          bad := bad.push m!"{name} ({mod}): cites differently named {head}"
      | none => bad := bad.push m!"{name} ({mod}): proof is not a `Proofs` theorem"
    | "Theorems", _ => bad := bad.push m!"{name} ({mod}): definition in a theorems module"
    | _, .thmInfo _ => bad := bad.push m!"{name} ({mod}): theorem in a definitions module"
    | _, _ => pure ()
  unless bad.isEmpty do throwError m!"layout violations:{indentD (MessageData.joinSep bad.toList "\n")}"
  logInfo m!"layout audit: {stated} stated theorems, each proved in a `Proofs` module"

#audit_layout

end ITreeTests.Audit
