import Lean

/-!
# `lemma`

`lemma` is `theorem` under another name, for helper facts that exist to prove other things; the
properties a test asserts stay `theorem`. It expands to `theorem` (like Mathlib's), so it takes the
same modifiers, attributes and docstrings, and linters and axiom audits see an ordinary theorem.
`Lint.BinderScope` imports this module, so every module of the package has it.
-/

namespace Lint.Lemma

open Lean

/-- `lemma` means the same as `theorem`: a helper fact rather than a headline result. -/
syntax (name := «lemma») declModifiers group("lemma " declId ppIndent(declSig) declVal) : command

/-- Rewrites the `lemma` node into the `theorem` declaration it stands for, so that later
changes to `theorem` carry over. -/
@[macro «lemma»] def expandLemma : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

end Lint.Lemma
