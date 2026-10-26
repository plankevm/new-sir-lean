import Lean
import ITree
import ITreeTests
import Host
import Sir
import SirTests
import Lint
import LintTests

/-! Package-wide gate: a linter runs only in modules that import it, so every module of the
package must have `Lint.BinderScope` among its transitive imports. -/

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

/-- Fails unless every module of the package is imported here and transitively imports
`Lint.BinderScope`. -/
elab "#audit_lint_imports" : command => do
  let env ← getEnv
  let idx : Std.HashMap Name Nat := env.header.moduleNames.foldl (init := {}) fun m n => m.insert n m.size
  let reaches (start : Nat) : Bool := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut todo := [env.header.moduleNames[start]!]
    while true do
      let some n := todo.head? | break
      todo := todo.tail
      if n == `Lint.BinderScope then return true
      if seen.contains n then continue
      seen := seen.insert n
      let some i := idx[n]? | continue
      todo := env.header.moduleData[i]!.imports.toList.map (·.module) ++ todo
    false
  let mut bad : Array Name := #[]
  let mods ← packageModules
  for m in mods do
    match idx[m]? with
    | none => bad := bad.push m
    | some i => unless m == `Lint.BinderScope || reaches i do bad := bad.push m
  unless bad.isEmpty do
    throwError m!"modules not imported by a library root, or not importing Lint.BinderScope: {bad}"
  logInfo m!"lint import audit: all {mods.size} modules import Lint.BinderScope"

#audit_lint_imports

end Audit
