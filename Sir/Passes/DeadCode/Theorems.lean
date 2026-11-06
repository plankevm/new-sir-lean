import Sir.Passes.DeadCode.Proofs

namespace Sir

theorem Function.liveBlocks_iff : ∀ (fn : Function), fn.WF → ∀ (b : BlockId),
    fn.liveBlocks[b.id]? = some true ↔ ∃ prev, fn.PathTo prev b :=
  Proofs.DeadCode.liveBlocks_iff

theorem Program.liveFunctions_iff : ∀ (p : Program), p.WF → ∀ (f : FunctionId),
    p.liveFunctions[f.id]? = some true ↔ p.Reachable p.init f ∨ p.Reachable p.main f :=
  Proofs.DeadCode.liveFunctions_iff

theorem Program.removeDeadCode_equiv : ∀ (p : Program), Safe p → Equiv p p.removeDeadCode :=
  fun _ => Proofs.DeadCode.removeDeadCode_equiv

theorem Program.removeDeadCode_safe : ∀ (p : Program), Safe p → Safe p.removeDeadCode :=
  fun _ => Proofs.DeadCode.removeDeadCode_safe

theorem Program.removeDeadCode_wf : ∀ (p : Program), p.WF → p.removeDeadCode.WF :=
  fun _ => Proofs.DeadCode.removeDeadCode_wf

end Sir
