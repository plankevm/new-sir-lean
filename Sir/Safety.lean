import Sir.Ir
import Sir.Layout
import Sir.Eval
import ITree.Outcome

open CoFree

namespace Sir

def RunSafe : CoFree Host.WorldE MemoryND (UB ⊕ Host.Outcome) → Prop :=
  fun sir => Deterministic sir ∧ ¬∃ ub : UB, HasOutcome sir (.res (.inl ub))

def MainSafe : (p : Program) → MainImmutablesMap p → Layout p → Prop :=
  fun p imms l => ∀ env static calldata w₀, RunSafe (p.run l (.call static calldata) env (Immutables.main imms) w₀)

def Safe : Program → Prop :=
  fun p =>
    ∀ l env ctorData imm w₀,
      w₀.Unset env.address →
      let run := p.run l (.creation ctorData) env imm w₀
      RunSafe run ∧
      ∀ mainCode w',
        HasOutcome run (.res <| .inr (.ret mainCode w')) →
        ∃ imms, l.withSetImmutables imms = mainCode ∧ MainSafe p imms l

end Sir
