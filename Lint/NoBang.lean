import Lean

/-!
# Panicking accessor linter

`get!`, `set!` and `xs[i]!` hide a bounds assumption behind a runtime panic and a silent default,
so a broken invariant shows up as junk data instead of a failed proof. `linter.noBang` rejects
them; use a bounds proof (`xs[i]`, `xs[i]'h`), `xs[i]?` with explicit handling, or carry the
evidence in the types. On by default; `Lint.BinderScope` imports this module, so every module of
the package has it.
-/

namespace Lint.NoBang

open Lean Elab Command

register_option linter.noBang : Bool := {
  defValue := true
  descr := "reject `get!`, `set!` and `xs[i]!`"
}

def banned : List String := ["get!", "set!", "getElem!"]

partial def hits (stx : Syntax) : Array Syntax :=
  match stx with
  | .ident _ _ n _ => match n with
    | .str _ s => if banned.contains s then #[stx] else #[]
    | _ => #[]
  | .node _ k args =>
    -- An instance defining its `getElem!` field is not a use.
    if k == ``Parser.Term.structInstLVal then #[] else
    let inner := args.foldl (· ++ hits ·) #[]
    if k == `«term__[_]_!» then inner.push stx else inner
  | _ => #[]

def noBangLinter : Linter where
  run stx := do
    unless Linter.getLinterValue linter.noBang (← Linter.getLinterOptions) do return
    for h in hits stx do
      Linter.logLint linter.noBang h
        m!"`{h.reprint.getD "" |>.trimAscii.toString}` can panic; use a bounds proof or `?` instead"

initialize addLinter noBangLinter

end Lint.NoBang
