import Sir.Memory
import Host.Interp

open Host

namespace Sir

def HostRead : HostOp → Prop
  | .selfbalance | .returndata | .balance _ | .extcode _ | .extcodehash _ | .sload _ | .tload _ => True
  | _ => False

def DeadExtra : EvalE.Op → Prop
  | .inl op => HostRead op
  | .inr (.read _ _) => True
  | .inr (.ub _) => True
  | .inr (.alloc _ _) => True
  | .inr _ => False

end Sir
