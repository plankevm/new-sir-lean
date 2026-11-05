import Sir.Ir
import Sir.Layout
import Sir.Eval
import ITree

open CoFree

namespace Sir

def RunSafe : CoFree Host.HostE MemoryND UB → Prop :=
  fun sir => Deterministic sir ∧ ¬∃ ub, HasOutcome sir (.res ub)

def MainSafe : (p : Program) → MainImmutablesMap p → Layout p → Prop :=
  fun p imms l => ∀ env, (h : env.mode.kind = .call) → RunSafe (p.runHost l env (h ▸ Immutables.main imms))

def Safe : Program → Prop :=
  fun p =>
    ∀ l env imm,
      env.mode.kind = .creation →
      let run := p.runHost l env imm
      RunSafe run ∧
      ∀ mainCode,
        HasOutcome run (.terminalOp <| .halt (.ret mainCode)) →
        ∃ imms, l.withSetImmutables imms = mainCode ∧ MainSafe p imms l

end Sir
