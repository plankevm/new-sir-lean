import Sir.Memory
import ITree.Same

/-! When two SIR runs behave the same, after `Mem` is handled (`exec`).

Allocations are branches (`Choice.placement`), so silent steps of `CoFree.Same`: each is
answered with every valid placement, on each side independently, and the runs must agree for
every pair of placements. Every host operation is visible and must match exactly, in the same
order. Undefined behavior (`fault (.ub _)`) is terminal and relates to any undefined behavior,
of any kind, and to nothing else; its kind is ignored because it may mention
placement-dependent addresses. `fault .malformed` is an ordinary visible operation.

`Same` is a partial equivalence, not an equivalence: a run whose visible behavior depends on
where something was allocated (say it stores a pointer) is not related even to itself.
`Deterministic t` says that it is, i.e. `t` does not leak placements. -/

namespace Sir

def HostOp.isUB : HostOp → Bool
  | .fault (.ub _) => true
  | _ => false

abbrev Undefined (op : HostOp) : Prop := op.isUB = true

abbrev Same {A B : Type} (RR : A → B → Prop) (t₁ : CoFree Exec A) (t₂ : CoFree Exec B) : Prop :=
  CoFree.Same Undefined RR t₁ t₂

def Deterministic {A : Type} (t : CoFree Exec A) : Prop :=
  Same Eq t t

end Sir
