import Sir.Equivalence.Proofs

namespace Sir

variable {p₁ p₂ p₃ : Program}

theorem Equiv.symm (h : Equiv p₁ p₂) : Equiv p₂ p₁ :=
  Proofs.equiv_symm h

theorem Equiv.trans (h₁ : Equiv p₁ p₂) (h₂ : Equiv p₂ p₃) : Equiv p₁ p₃ :=
  Proofs.equiv_trans h₁ h₂

theorem Equiv.refl_left (h : Equiv p₁ p₂) : Equiv p₁ p₁ :=
  Proofs.equiv_refl_left h

end Sir
