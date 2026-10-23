import Lint.BinderScope

namespace LintTests.BinderScope

set_option linter.binderScope true
set_option warningAsError false

-- The motivating bug: `res` scopes over the conclusion, so it is one constructor argument.
/--
@ +2:20...46
warning: binder scope: `∀ res : Nat,` extends over the whole connective after it; write `(∀ res : Nat, P res → Bad P)` or `∀ res : Nat, (P res → Bad P)` (nested)

Note: This linter can be disabled with `set_option linter.binderScope false`
-/
#guard_msgs (positions := true) in
inductive Bad (P : Nat → Prop) : Prop
  | impure : True → ∀ res : Nat, P res → Bad P

#guard_msgs in
inductive Good (P : Nat → Prop) : Prop
  | premise : True → (∀ res : Nat, P res) → Good P
  | argument : True → ∀ res : Nat, (P res → Good P)
  | inBinder (h : ∀ res : Nat, P res → True) : Good P

/--
@ +1:18...42
warning: binder scope: `∀ x : Nat,` extends over the whole connective after it; write `(∀ x : Nat, x = x → x = x)` or `∀ x : Nat, (x = x → x = x)` (leading, in Lean.Parser.Command.declSig)

Note: This linter can be disabled with `set_option linter.binderScope false`
-/
#guard_msgs (positions := true) in
theorem leading : ∀ x : Nat, x = x → x = x := fun _ h => h

/--
@ +1:30...53
warning: binder scope: `∃ x : Nat,` extends over the whole connective after it; write `(∃ x : Nat, x = 0 ∧ True)` or `∃ x : Nat, (x = 0 ∧ True)` (nested)

Note: This linter can be disabled with `set_option linter.binderScope false`
-/
#guard_msgs (positions := true) in
theorem nestedExists : True → ∃ x : Nat, x = 0 ∧ True := fun _ => ⟨0, rfl, trivial⟩

/--
@ +1:23...48
warning: binder scope: `(x : Nat) →` extends over the whole connective after it; write `((x : Nat) → x = x ∨ False)` or `(x : Nat) → (x = x ∨ False)` (leading, in Lean.Parser.Command.declValSimple)

Note: This linter can be disabled with `set_option linter.binderScope false`
-/
#guard_msgs (positions := true) in
def depArrow : Prop := (x : Nat) → x = x ∨ False

#guard_msgs in
theorem fixedLeading : ∀ x : Nat, (x = x → x = x) := fun _ h => h

#guard_msgs in
theorem noConnective : ∀ x : Nat, ∀ y : Nat, x + y = y + x := Nat.add_comm

end LintTests.BinderScope
