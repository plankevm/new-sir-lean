import Lint.BinderScope
import Sir.Ir
import Sir.Safety
import Sir.WellFormed

namespace Sir

def TotalPass := Program → Program

def TotalPassSound (pass : TotalPass) : Prop :=
  ∀ (p : Program), p.WF → Safe p → let p' := pass p; Equiv p p' ∧ Safe p' ∧ p'.WF

end Sir
