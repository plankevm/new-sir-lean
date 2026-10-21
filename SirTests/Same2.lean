import Sir.Same2.Proofs
import SirTests.Same

/-! The examples of `SirTests.Same`, for `Same2`. -/

namespace SirTests.Same2

open Sir SirTests.Same
open Sir.Same2.Proofs (same2_iff_same)

theorem mallocs_same_mallocsAny : Same2 (run mallocs) (run mallocsAny) :=
  same2_iff_same.mpr Same.mallocs_same_mallocsAny

theorem mallocs_same_stops : Same2 (run mallocs) (run stops) :=
  same2_iff_same.mpr Same.mallocs_same_stops

theorem mallocs_deterministic : Same2 (run mallocs) (run mallocs) :=
  same2_iff_same.mpr Same.mallocs_deterministic

theorem stores_same_jumpsThenStores : Same2 (run (stores 1)) (run jumpsThenStores) :=
  same2_iff_same.mpr Same.stores_same_jumpsThenStores

theorem stores_same_readsEnvThenStores : Same2 (run (stores 1)) (run readsEnvThenStores) :=
  same2_iff_same.mpr Same.stores_same_readsEnvThenStores

theorem switchUB_same_readUB : Same2 (run switchUB) (run readUB) :=
  same2_iff_same.mpr Same.switchUB_same_readUB

theorem stores_not_same : ¬Same2 (run (stores 1)) (run (stores 2)) :=
  fun h => Same.stores_not_same (same2_iff_same.mp h)

theorem switchUB_not_same_stops : ¬Same2 (run switchUB) (run stops) :=
  fun h => Same.switchUB_not_same_stops (same2_iff_same.mp h)

theorem leaks_not_deterministic : ¬Same2 (run leaks) (run leaks) :=
  fun h => Same.leaks_not_deterministic (same2_iff_same.mp h)

end SirTests.Same2
