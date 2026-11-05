import Sir.Layout.Proofs

namespace Sir

variable {p : Program}

theorem Layout.extractImmutables_eq_map (l : Layout p) (b : ByteArray) :
    l.extractImmutables b = (l.toMainImmutablesMap b).map fun m => (m.tail, m.slots.toArray) :=
  Proofs.extractImmutables_eq_map l b

theorem Layout.toMainImmutablesMap_eq_some_iff (l : Layout p) (b : ByteArray) (imms : MainImmutablesMap p) :
    l.toMainImmutablesMap b = some imms ↔ l.withSetImmutables imms = b :=
  Proofs.toMainImmutablesMap_eq_some_iff l b imms

theorem Layout.extractImmutables_withSetImmutables (l : Layout p) (imms : MainImmutablesMap p) :
    l.extractImmutables (l.withSetImmutables imms) = some (imms.tail, imms.slots.toArray) :=
  Proofs.extractImmutables_withSetImmutables l imms

theorem Layout.extractImmutables_isSome_iff (l : Layout p) (b : ByteArray) :
    (l.extractImmutables b).isSome ↔ ∃ imms, l.withSetImmutables imms = b :=
  Proofs.extractImmutables_isSome_iff l b

end Sir
