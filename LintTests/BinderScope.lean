import Lint.BinderScope

namespace LintTests.BinderScope

set_option warningAsError false

-- The motivating bug: `res` scopes over the conclusion, so it is one constructor argument.
/--
@ +2:20...46
warning: binder scope: `∀ res : Nat,` extends over the whole connective after it; write `(∀ res : Nat, P res → Bad P)` or `∀ res : Nat, (P res → Bad P)`

Note: This linter can be disabled with `set_option linter.binderScope false`
-/
#guard_msgs (positions := true) in
inductive Bad (P : Nat → Prop) : Prop
  | impure : True → ∀ res : Nat, P res → Bad P

/--
@ +2:19...43
warning: binder scope: `∀ n : Nat,` extends over the whole connective after it; write `(∀ n : Nat, n = n → BadCo)` or `∀ n : Nat, (n = n → BadCo)`

Note: This linter can be disabled with `set_option linter.binderScope false`
-/
#guard_msgs (positions := true) in
coinductive BadCo : Prop
  | step : BadCo → ∀ n : Nat, n = n → BadCo

#guard_msgs in
inductive Good (P : Nat → Prop) : Prop
  | premise : True → (∀ res : Nat, P res) → Good P
  | argument : True → ∀ res : Nat, (P res → Good P)
  | beforeColon (res : Nat) : True → P res → Good P
  | inBinder (h : ∀ res : Nat, P res → True) : Good P
  | leading : ∀ res : Nat, P res → Good P
  | leadingImplicit {res : Nat} : P res → Good P

-- Outside constructors, binders are not checked.
#guard_msgs in
theorem leading : ∀ x : Nat, x = x → x = x := fun _ h => h

#guard_msgs in
theorem nestedExists : True → ∃ x : Nat, x = 0 ∧ True := fun _ => ⟨0, rfl, trivial⟩

#guard_msgs in
def depArrow : Prop := (x : Nat) → x = x ∨ False

end LintTests.BinderScope
