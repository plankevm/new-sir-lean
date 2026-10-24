import Sir.Memory
import ITree.Same

/-! When two SIR runs behave the same, after `Mem` is handled (`exec`).

Allocations are branches (`Choice.placement`), so unobserved steps of `CoFree.Same`: each is
answered with every valid placement, on each side independently, and the runs must agree for
every pair of placements. Every host operation is visible and must match exactly, in the same
order. A fault (`fault (.ub u)`, `fault .malformed`) has no answer, so it ends the run and
relates only to the same fault. In particular undefined behavior of different kinds, or with
different arguments (which may mention placement-dependent addresses), is not related.

`Same` is a partial equivalence, not an equivalence: a run whose visible behavior depends on
where something was allocated (say it stores a pointer) is not related even to itself.
`Deterministic t` says that it is, i.e. `t` does not leak placements. -/

namespace Sir

abbrev Same {A B : Type} (Ret : A → B → Prop) (t₁ : CoFree Exec A) (t₂ : CoFree Exec B) : Prop :=
  CoFree.Same Ret t₁ t₂

def Deterministic {A : Type} (t : CoFree Exec A) : Prop :=
  Same Eq t t

end Sir
