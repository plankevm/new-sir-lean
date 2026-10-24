import Sir.Same2.Proofs
import SirTests.Same

/-! The examples of `SirTests.Same` that carry over to `Same2`. -/

namespace SirTests.Same2

open Sir SirTests.Same
open Sir.Same2.Proofs (same2_of_same)

theorem mallocs_same_mallocsAny : Same2 (run mallocs) (run mallocsAny) :=
  same2_of_same Same.mallocs_same_mallocsAny

theorem mallocs_same_stops : Same2 (run mallocs) (run stops) :=
  same2_of_same Same.mallocs_same_stops

theorem mallocs_deterministic : Same2 (run mallocs) (run mallocs) :=
  same2_of_same Same.mallocs_deterministic

theorem stores_same_jumpsThenStores : Same2 (run (stores 1)) (run jumpsThenStores) :=
  same2_of_same Same.stores_same_jumpsThenStores

theorem stores_same_readsEnvThenStores : Same2 (run (stores 1)) (run readsEnvThenStores) :=
  same2_of_same Same.stores_same_readsEnvThenStores

theorem switchUB_same_switchUB : Same2 (run switchUB) (run switchUB) :=
  same2_of_same Same.switchUB_same_switchUB

end SirTests.Same2
