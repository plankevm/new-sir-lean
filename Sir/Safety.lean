import Sir.Ir
import Sir.Layout
import Sir.Eval
import ITree.Outcome

open CoFree

namespace Sir

def RunSafe {O : Type}: CoFree Host.WorldE MemoryND (UB ⊕ O) → Prop :=
  fun sir => Deterministic sir ∧ ¬∃ ub : UB, HasResOutcome sir (.inl ub)

def MainSafe  (p : Program) (imms :  MainImmutablesMap p) (l : Layout p) : Prop :=
  ∀ env static calldata w₀, RunSafe (p.runMain l imms static calldata env w₀)

def InitSafe  (p : Program) (l : Layout p) : Prop :=
  ∀ env ctorArgs w₀, RunSafe (p.runInit l ctorArgs env w₀)

def Safe : Program → Prop :=
  fun p =>
    ∀ l env ctorArgs w₀,
      w₀.Unset env.address →
      let init := p.runInit l ctorArgs env w₀
      RunSafe init ∧
      ∀ imms w', HasResOutcome init (.inr (.ret p imms w')) → MainSafe p imms l

end Sir
