import Sir.Layout.Proofs

namespace Sir

variable {p : Program}

theorem Layout.extractImmutables_eq_map (l : Layout p) (b : ByteArray) :
    l.extractImmutables b = (l.toMainImmutables b).map fun m => (m.tail, m.slots) :=
  Proofs.extractImmutables_eq_map l b

theorem Layout.toMainImmutables_wf (l : Layout p) (b : ByteArray) (imms : MainImmutables)
    (h : l.toMainImmutables b = some imms) : imms.WF p :=
  Proofs.toMainImmutables_wf l b imms h

theorem Layout.toMainImmutables_eq_some_iff (l : Layout p) (b : ByteArray) (imms : MainImmutables) :
    l.toMainImmutables b = some imms ↔ l.withSetImmutables imms = some b :=
  Proofs.toMainImmutables_eq_some_iff l b imms

theorem Layout.extractImmutables_withSetImmutables (l : Layout p) (imms : MainImmutables) (b : ByteArray)
    (h : l.withSetImmutables imms = some b) :
    l.extractImmutables b = some (imms.tail, imms.slots) :=
  Proofs.extractImmutables_withSetImmutables l imms b h

theorem Layout.extractImmutables_isSome_iff (l : Layout p) (b : ByteArray) :
    (l.extractImmutables b).isSome ↔ ∃ imms : MainImmutables, l.withSetImmutables imms = some b :=
  Proofs.extractImmutables_isSome_iff l b

end Sir
