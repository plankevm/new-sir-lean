import Sir.Ir
import Sir.Layout
import Sir.Eval
import Sir.Equivalence
import ITree.Outcome

open CoFree

namespace Sir

def MainSafe  (p : Program) (l : Layout p) (imms : MainImmutables) : Prop :=
  ∀ e static cd w₀, Deterministic (p.runMain l imms static cd e w₀)

def Safe (p : Program) : Prop :=
  Equiv p p ∧
  ∀ l e c w₀,
    w₀.Unset e.address →
    let init := p.runInit l c e w₀
    Deterministic init ∧
    ∀ imms w', HasResOutcome init (.inr (.ret imms w')) → imms.WF p ∧ MainSafe p l imms

end Sir
