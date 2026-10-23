import Lean

/-!
# Binder scope linter

`∀ x, A → B` reads as `∀ x, (A → B)`: a binder extends as far right as possible. In an
inductive constructor, `h → ∀ r, P r → C` therefore binds `r` over the conclusion `C`, making
`r` one constructor argument (an `∃`) instead of the intended premise `(∀ r, P r) → C`.

`linter.binderScope` flags, in constructor types only, every `∀`/`∃`/`(x : A) →` binder that is
not part of the type's leading binder telescope and whose body is, at top level, a logical
connective (`→`, `∧`, `∨`, `↔`), unless the binder ends at a closing bracket, so the reader sees
where its scope ends. Fixes: `(∀ x, A → B)`, `∀ x, (A → B)`, or move `x` before the colon.
Leading binders elsewhere are idiomatic and not flagged.
-/

namespace Lint.BinderScope

open Lean Elab Command

register_option linter.binderScope : Bool := {
  defValue := false
  descr := "flag `∀`/`∃` binders whose body is an unparenthesized `→`/`∧`/`∨`/`↔`"
}

/-- The body of a binder notation: `∀ xs, body`, `∃ xs, body`, `(x : A) → body`, … -/
def binderBody? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Parser.Term.depArrow then some stx[2] else
  match stx with
  | .node _ _ args =>
    let atom (s : Syntax) := if s.isAtom then s.getAtomVal.trimAscii.toString else ""
    if args.size ≥ 3 && atom args[args.size - 2]! == "," &&
        ["∀", "∃", "∃!", "Π", "forall", "exists"].contains (atom args[0]!)
    then some args.back! else none
  | _ => none

def connectives : List SyntaxNodeKind :=
  [``Parser.Term.arrow, `«term_∧_», `«term_∨_», `«term_↔_», `«term_/\_», `«term_\/_», `«term_<->_»]

def closers : List String := [")", "]", "}", "⟩", "⦄", "⟧", "⦘", "⟯"]

/-- Wrapper nodes a binder's scope can end through. -/
def transparent (k : SyntaxNodeKind) : Bool :=
  k == nullKind || k == ``Parser.Term.typeSpec

/-- Applications and infix/postfix notations: a binder inside them is nested. -/
def isOperator (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Term.app || k == ``Parser.Term.arrow || "«term_".isPrefixOf k.toString

structure Hit where
  stx : Syntax
  /-- `none` if nested in an operator; otherwise the kind of the node the binder chain is the
  whole of (a declaration or constructor signature, a `have` type, a definition body, …). -/
  leading : Option SyntaxNodeKind
  inCtor : Bool

/-- `follow` is the first token after `stx` before the end of its nearest non-transparent
ancestor; `anc` are the ancestors' kinds, innermost first. -/
partial def visit (stx : Syntax) (anc : List SyntaxNodeKind) (follow : Option String) :
    StateM (Array Hit) Unit := do
  let .node _ k args := stx | return
  if let some body := binderBody? stx then
    if connectives.any body.isOfKind && !(follow.any closers.contains) then
      let up := anc.dropWhile fun a =>
        transparent a || a == ``Parser.Term.depArrow || a == ``Parser.Term.forall ||
          "«term∃".isPrefixOf a.toString || "«term∀".isPrefixOf a.toString
      let leading := match up with
        | a :: _ => if isOperator a then none else some a
        | [] => some nullKind
      modify (·.push { stx, leading, inCtor := anc.contains ``Parser.Command.ctor })
  for i in [:args.size] do
    let next := (args.extract (i + 1) args.size).findSome? fun s =>
      s.getHead?.bind fun h => if h.isAtom then some h.getAtomVal.trimAscii.toString else some ""
    let follow := next <|> if transparent k then follow else none
    visit args[i]! (k :: anc) follow

def hits (stx : Syntax) : Array Hit :=
  ((visit stx [] none).run #[]).2

def message (h : Hit) : MessageData :=
  let binder := (h.stx.setArg (h.stx.getNumArgs - 1) mkNullNode).reprint.getD "∀ x,"
    |>.trimAscii.toString
  let body := (binderBody? h.stx).bind (·.reprint) |>.getD "" |>.trimAscii.toString
  let body := if body.length ≤ 40 then body else "…"
  m!"binder scope: `{binder}` extends over the whole connective after it; write \
    `({binder} {body})` or `{binder} ({body})`"

def binderScopeLinter : Linter where
  run stx := do
    unless Linter.getLinterValue linter.binderScope (← Linter.getLinterOptions) do return
    for h in hits stx do
      unless h.inCtor && h.leading.isNone do continue
      Linter.logLint linter.binderScope h.stx (message h)

initialize addLinter binderScopeLinter

end Lint.BinderScope
