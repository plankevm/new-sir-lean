import Sir.Memory.DeadAlloc.Proofs

open Host CoFree

namespace Sir

theorem Same.removeDeadAllocs : ∀ {α β : Type} {N : NonDeterminism} {Ret : α → β → Prop}
    {bad : β → Prop} (F : UB ⊕ Host.Outcome → β), (∀ u, bad (F (.inl u))) →
    ∀ (x : CoFree WorldE N α) {m₁ m₂ : SirM Empty} (self : Address) (w₀ : World),
      Skip DeadExtra (fun _ => False) Eq m₁ m₂ →
      NoBad bad ((interpHost self w₀ (interpMem m₁)).bind fun r => CoFree.pure (F r)) →
      Same Ret x ((interpHost self w₀ (interpMem m₁)).bind fun r => CoFree.pure (F r)) →
      Same Ret x ((interpHost self w₀ (interpMem m₂)).bind fun r => CoFree.pure (F r)) :=
  Proofs.DeadAlloc.Same.removeDeadAllocs

end Sir
