import Lean
import Sir
import SirTests.Same
import SirTests.Safe

namespace SirTests.Audit

open Lean Elab Command

/-- Fails unless every declaration of the `Sir` library and of `SirTests.Same`,
`SirTests.Same2` and `SirTests.Safe` uses only `propext`, `Quot.sound` and `Classical.choice`;
in particular no `sorryAx`. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let mut bad : Array (Name × Name) := #[]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    unless (env.getModuleIdxFor? name).any fun idx =>
        let mod := env.header.moduleNames[idx.toNat]!
        mod.getRoot == `Sir || mod == `SirTests.Same || mod == `SirTests.Same2 ||
          mod == `SirTests.Safe do continue
    checked := checked + 1
    for ax in ← liftCoreM (collectAxioms name) do
      unless allowed.contains ax do bad := bad.push (name, ax)
  unless bad.isEmpty do throwError m!"disallowed axioms: {bad}"
  logInfo m!"axiom audit: {checked} declarations use only propext, Quot.sound, Classical.choice"

#audit_axioms

end SirTests.Audit
