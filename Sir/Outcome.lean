import Sir.Memory
import Host.Outcome

/-! Which SIR programs are safe. Outcomes and safety of a run are `Host`'s: a run of `exec` is a
`CoFree Exec Empty` with `Exec = WorldE`, the same as any other IR's once its own effects are
handled. -/

namespace Sir

open Host

/-- An entry point is safe for every frame environment (calldata, caller, …), every initial
storage and world, and every value of the immutables. The layout is fixed by the compiler, so it
is a parameter. -/
def Program.Safe (p : Program) (layout : Layout) (e : Entry) : Prop :=
  ∀ imm env s, Host.Safe (exec p layout imm env e s)

end Sir
