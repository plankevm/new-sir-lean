import Lean
import ITree
import ITreeTests
import Host
import Sir
import SirTests
import Lint
import LintTests

/-! Package-wide gates: a linter runs only in modules that import it, so every module of the
package must have `Lint.BinderScope` among its transitive imports; and every declaration of
the package may depend only on the standard axioms. -/

namespace Audit

open Lean Elab Command

def libs : List String := ["ITree", "ITreeTests", "Host", "Sir", "SirTests", "Lint", "LintTests"]

/-- The module names of every `.lean` file of the package's libraries. -/
def packageModules : IO (Array Name) := do
  let mut mods := #[]
  for lib in libs do
    mods := mods.push lib.toName
    if ← System.FilePath.isDir lib then
      for f in ← System.FilePath.walkDir lib do
        if f.extension == some "lean" then
          mods := mods.push ((f.withExtension "").components.foldl Name.str .anonymous)
  pure mods

/-- `Lint.BinderScope` and the modules it imports, which cannot import it back. -/
def lintBase : List Name := [`Lint.BinderScope, `Lint.Lemma, `Lint.NoBang]

/-- Fails unless every module of the package is imported here and transitively imports
`Lint.BinderScope` (or is in `lintBase`). -/
elab "#audit_lint_imports" : command => do
  let env ← getEnv
  let idx : Std.HashMap Name Nat := env.header.moduleNames.foldl (init := {}) fun m n => m.insert n m.size
  let reaches (start : Name) : Bool := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut todo := [start]
    while true do
      let some n := todo.head? | break
      todo := todo.tail
      if n == `Lint.BinderScope then return true
      if seen.contains n then continue
      seen := seen.insert n
      let some i := idx[n]? | continue
      let some data := env.header.moduleData[i]? | continue
      todo := data.imports.toList.map (·.module) ++ todo
    false
  let mut bad : Array Name := #[]
  let mods ← packageModules
  for m in mods do
    unless idx.contains m && (lintBase.contains m || reaches m) do bad := bad.push m
  unless bad.isEmpty do
    throwError m!"modules not imported by a library root, or not importing Lint.BinderScope: {bad}"
  logInfo m!"lint import audit: all {mods.size} modules import Lint.BinderScope"

#audit_lint_imports

/-- Modules additionally allowed the axioms `native_decide`/`bv_decide` add (named
`<decl>._native.<tactic>.ax_<n>`, see `Lean.Meta.nativeEqTrue`). A declaration in another
module that cites such a check still fails. No module uses them yet. -/
def nativeModules : List Name := []

/-- Fails unless every declaration of every package module uses only `propext`, `Quot.sound`
and `Classical.choice` (plus native-evaluation axioms in `nativeModules`); in particular
no `sorryAx`. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let mods : Std.HashSet Name := .ofArray (← packageModules)
  let mut bad : Array MessageData := #[]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless mods.contains mod do continue
    checked := checked + 1
    for ax in ← liftCoreM (collectAxioms name) do
      unless allowed.contains ax || (ax.components.contains `_native && nativeModules.contains mod) do
        bad := bad.push m!"{name} ({mod}) uses {ax}"
  unless bad.isEmpty do throwError m!"disallowed axioms:{indentD (MessageData.joinSep bad.toList "\n")}"
  logInfo m!"axiom audit: {checked} declarations use only propext, Quot.sound, Classical.choice"

#audit_axioms

end Audit
