import Sir.Deploy

namespace Sir

open Host CoFree

theorem PlainRel.deployRel {p : Program} {c₁ c₂ : Code p} (hm : p.MainValid) {o₁ o₂ : Outcome}
    (h : PlainRel p c₁ c₂ o₁ o₂) : DeployRel p c₁ c₂ o₁ o₂ := by
  cases o₁ <;> cases o₂ <;> simp only [PlainRel, DeployRel] at h ⊢
  case ret.ret r₁ st₁ r₂ st₂ =>
    obtain ⟨hst, ht, imm, h₁, h₂⟩ := h
    exact ⟨hst, imm, imm, h₁, h₂, hm c₁ c₂ r₁ r₂ imm h₁ h₂ ht⟩
  all_goals exact h

/-- An `init` that returns the same immutables and appended data under every layout, with a
`main` that does not depend on its layout, is valid. -/
theorem Program.initValid_of_plain {p : Program} (hi : p.InitPlain) (hm : p.MainValid) :
    p.InitValid :=
  fun c₁ c₂ env args s => Same.mono (fun _ _ => PlainRel.deployRel hm) (hi c₁ c₂ env args s)

end Sir
