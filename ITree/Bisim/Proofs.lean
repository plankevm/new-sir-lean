import ITree.Bisim
import ITree.Same.Theorems
import ITree.Outcome
import ITree.Machine.Theorems
import ITree.Reaches.Theorems
import ITree.Step.Theorems

universe u

namespace CoFree.Proofs

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A B C D : Type u}

section Basic

variable {ρ : OpRel E} {Ret : A → B → Prop}

theorem stepRel_mono {R R' : CoFree E N A → CoFree E N B → Prop} (hR : ∀ x y, R x y → R' x y)
    {s₁ : Step E N A (CoFree E N A)} {s₂ : Step E N B (CoFree E N B)}
    (h : StepRel ρ Ret R s₁ s₂) : StepRel ρ Ret R' s₁ s₂ := by
  cases s₁ <;> cases s₂ <;> simp only [StepRel] at h ⊢
  · exact h
  · exact hR _ _ h
  · exact ⟨h.1, fun r₁ r₂ hr => hR _ _ (h.2 r₁ r₂ hr)⟩
  · exact ⟨h.1, fun r₁ r₂ hr => hR _ _ (h.2 r₁ r₂ hr)⟩

theorem stepRel_mono_ret {Ret' : A → B → Prop} (hRet : ∀ a b, Ret a b → Ret' a b)
    {R : CoFree E N A → CoFree E N B → Prop}
    {s₁ : Step E N A (CoFree E N A)} {s₂ : Step E N B (CoFree E N B)}
    (h : StepRel ρ Ret R s₁ s₂) : StepRel ρ Ret' R s₁ s₂ := by
  cases s₁ <;> cases s₂ <;> simp only [StepRel] at h ⊢
  · exact hRet _ _ h
  all_goals exact h

theorem Bisim.unfold {m₁ : CoFree E N A} {m₂ : CoFree E N B} (h : Bisim ρ Ret m₁ m₂) :
    StepRel ρ Ret (Bisim ρ Ret) m₁.observe m₂.observe := by
  obtain ⟨R, hm, hR⟩ := h
  exact stepRel_mono (fun x y hxy => ⟨R, hxy, hR⟩) (hR _ _ hm)

theorem Bisim.coind (R : CoFree E N A → CoFree E N B → Prop)
    (hR : ∀ x y, R x y → StepRel ρ Ret (fun a b => R a b ∨ Bisim ρ Ret a b) x.observe y.observe)
    {m₁ : CoFree E N A} {m₂ : CoFree E N B} (h : R m₁ m₂) : Bisim ρ Ret m₁ m₂ := by
  refine ⟨fun a b => R a b ∨ Bisim ρ Ret a b, .inl h, fun x y hxy => ?_⟩
  rcases hxy with hxy | hxy
  · exact hR x y hxy
  · exact stepRel_mono (fun _ _ => .inr) (Bisim.unfold hxy)

theorem Bisim.fold {m₁ : CoFree E N A} {m₂ : CoFree E N B}
    (h : StepRel ρ Ret (Bisim ρ Ret) m₁.observe m₂.observe) : Bisim ρ Ret m₁ m₂ :=
  Bisim.coind (fun x y => x = m₁ ∧ y = m₂)
    (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact stepRel_mono (fun _ _ => .inr) h) ⟨rfl, rfl⟩

theorem Bisim.congr {m₁ m₁' : CoFree E N A} {m₂ m₂' : CoFree E N B}
    (he₁ : m₁.observe = m₁'.observe) (he₂ : m₂.observe = m₂'.observe) (h : Bisim ρ Ret m₁ m₂) :
    Bisim ρ Ret m₁' m₂' := by
  apply Bisim.fold
  rw [← he₁, ← he₂]
  exact Bisim.unfold h

theorem Bisim.mono {Ret' : A → B → Prop} (hRet : ∀ a b, Ret a b → Ret' a b)
    {m₁ : CoFree E N A} {m₂ : CoFree E N B} (h : Bisim ρ Ret m₁ m₂) : Bisim ρ Ret' m₁ m₂ := by
  obtain ⟨R, hm, hR⟩ := h
  exact ⟨R, hm, fun x y hxy => stepRel_mono_ret hRet (hR x y hxy)⟩

theorem Bisim.pure {a : A} {b : B} (h : Ret a b) :
    Bisim ρ Ret (CoFree.pure a : CoFree E N A) (CoFree.pure b) := by
  apply Bisim.fold
  rw [observe_pure, observe_pure]
  exact h

theorem Bisim.refl {Ret : A → A → Prop} (hRet : ∀ a, Ret a a) (m : CoFree E N A) :
    Bisim (OpRel.eq E) Ret m m := by
  refine ⟨Eq, rfl, fun x y hxy => ?_⟩
  subst hxy
  cases x.observe with
  | pure a => exact hRet a
  | silent m => exact rfl
  | impure o k => exact ⟨rfl, fun r₁ r₂ hr => by cases hr; rfl⟩
  | branch c k => exact ⟨rfl, fun r₁ r₂ hr => by cases hr; rfl⟩

theorem Bisim.symm {m₁ : CoFree E N A} {m₂ : CoFree E N A} (h : Bisim (OpRel.eq E) Eq m₁ m₂) :
    Bisim (OpRel.eq E) Eq m₂ m₁ := by
  obtain ⟨R, hm, hR⟩ := h
  refine ⟨fun x y => R y x, hm, fun x y hxy => ?_⟩
  have h := hR y x hxy
  generalize x.observe = s₁ at h ⊢
  generalize y.observe = s₂ at h ⊢
  cases s₁ <;> cases s₂ <;> simp only [StepRel, OpRel.eq] at h ⊢
  · exact h.symm
  · exact h
  · obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, fun r₁ r₂ hr => h r₂ r₁ hr.symm⟩
  · obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, fun r₁ r₂ hr => h r₂ r₁ hr.symm⟩

end Basic

section Bind

variable {ρ : OpRel E}

theorem Bisim.bind {Ret : A → B → Prop} {Ret' : C → D → Prop} {m₁ : CoFree E N A}
    {m₂ : CoFree E N B} {g₁ : A → CoFree E N C} {g₂ : B → CoFree E N D}
    (h : Bisim ρ Ret m₁ m₂) (hg : ∀ a b, Ret a b → Bisim ρ Ret' (g₁ a) (g₂ b)) :
    Bisim ρ Ret' (m₁.bind g₁) (m₂.bind g₂) := by
  refine Bisim.coind (fun x y => ∃ n₁ n₂, Bisim ρ Ret n₁ n₂ ∧ x = n₁.bind g₁ ∧ y = n₂.bind g₂)
    (fun x y ⟨n₁, n₂, hn, hx, hy⟩ => ?_) ⟨m₁, m₂, h, rfl, rfl⟩
  subst hx hy
  rw [observe_bind, observe_bind]
  have hs := Bisim.unfold hn
  generalize n₁.observe = s₁ at hs ⊢
  generalize n₂.observe = s₂ at hs ⊢
  cases s₁ <;> cases s₂ <;> simp only [StepRel, bindStep] at hs ⊢
  · exact stepRel_mono (fun _ _ => .inr) (Bisim.unfold (hg _ _ hs))
  · exact .inl ⟨_, _, hs, rfl, rfl⟩
  · exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, hs.2 r₁ r₂ hr, rfl, rfl⟩⟩
  · exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, hs.2 r₁ r₂ hr, rfl, rfl⟩⟩

theorem Bisim.mapOps {ρ' : OpRel F} {e : Effect.Map E F} {nd : NonDeterminism.Map N M}
    {Ret : A → B → Prop} {m₁ : CoFree E N A} {m₂ : CoFree E N B}
    (hop : ∀ o₁ o₂, ρ.op o₁ o₂ → ρ'.op (e.op o₁) (e.op o₂))
    (hresp : ∀ o₁ o₂ r₁ r₂, ρ.op o₁ o₂ → ρ'.resp (e.op o₁) (e.op o₂) r₁ r₂ →
      ρ.resp o₁ o₂ (e.resp o₁ r₁) (e.resp o₂ r₂))
    (h : Bisim ρ Ret m₁ m₂) : Bisim ρ' Ret (m₁.mapOps e nd) (m₂.mapOps e nd) := by
  refine Bisim.coind (fun x y => ∃ n₁ n₂, Bisim ρ Ret n₁ n₂ ∧ x = n₁.mapOps e nd ∧ y = n₂.mapOps e nd)
    (fun x y ⟨n₁, n₂, hn, hx, hy⟩ => ?_) ⟨m₁, m₂, h, rfl, rfl⟩
  subst hx hy
  rw [observe_mapOps, observe_mapOps]
  have hs := Bisim.unfold hn
  generalize n₁.observe = s₁ at hs ⊢
  generalize n₂.observe = s₂ at hs ⊢
  cases s₁ <;> cases s₂ <;> simp only [StepRel] at hs ⊢
  · exact hs
  · exact .inl ⟨_, _, hs, rfl, rfl⟩
  · exact ⟨hop _ _ hs.1, fun r₁ r₂ hr => .inl ⟨_, _, hs.2 _ _ (hresp _ _ _ _ hs.1 hr), rfl, rfl⟩⟩
  · obtain ⟨rfl, hk⟩ := hs
    exact ⟨rfl, fun r₁ r₂ hr => by cases hr; exact .inl ⟨_, _, hk _ _ HEq.rfl, rfl, rfl⟩⟩

end Bind

section Iter

variable {ρ : OpRel E} {S₁ S₂ : Type u}

theorem Bisim.iter {Ret : A → B → Prop} (RS : S₁ → S₂ → Prop)
    {g₁ : S₁ → CoFree E N (IterStep S₁ A)} {g₂ : S₂ → CoFree E N (IterStep S₂ B)}
    (hg : ∀ s₁ s₂, RS s₁ s₂ → Bisim ρ (IterRel RS Ret) (g₁ s₁) (g₂ s₂))
    {s₁ : S₁} {s₂ : S₂} (h : RS s₁ s₂) : Bisim ρ Ret (CoFree.iter s₁ g₁) (CoFree.iter s₂ g₂) := by
  refine Bisim.coind (fun x y => ∃ i₁ p₁ i₂ p₂, x = (CoFree.iter s₁ g₁).startAt ⟨i₁, p₁⟩ ∧
      y = (CoFree.iter s₂ g₂).startAt ⟨i₂, p₂⟩ ∧
      Bisim ρ (IterRel RS Ret) ((g₁ i₁).atPos p₁) ((g₂ i₂).atPos p₂))
    (fun x y ⟨i₁, p₁, i₂, p₂, hx, hy, hb⟩ => ?_)
    ⟨s₁, (g₁ s₁).initPos, s₂, (g₂ s₂).initPos, rfl, rfl, by
      rw [atPos_initPos, atPos_initPos]; exact hg _ _ h⟩
  subst hx hy
  rw [observe_iter_startAt, observe_iter_startAt]
  have hs := Bisim.unfold hb
  rw [observe_atPos, observe_atPos] at hs
  generalize (g₁ i₁).stepAt p₁ = s₁ at hs ⊢
  generalize (g₂ i₂).stepAt p₂ = s₂ at hs ⊢
  cases s₁ <;> cases s₂ <;> simp only [StepRel, Step.map] at hs ⊢
  · rename_i a b
    cases a <;> cases b <;> simp only [IterRel] at hs ⊢
    · exact .inl ⟨_, (g₁ _).initPos, _, (g₂ _).initPos, rfl, rfl, by
        rw [atPos_initPos, atPos_initPos]; exact hg _ _ hs⟩
    · exact hs
  · exact .inl ⟨_, _, _, _, rfl, rfl, hs⟩
  · exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, _, _, rfl, rfl, hs.2 r₁ r₂ hr⟩⟩
  · exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, _, _, rfl, rfl, hs.2 r₁ r₂ hr⟩⟩

end Iter

section Loops

variable {ρ : OpRel E}

theorem Bisim.loop {β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) {Ret : β₁ → β₂ → Prop}
    {f₁ : Unit → β₁ → CoFree E N (ForInStep β₁)} {f₂ : Unit → β₂ → CoFree E N (ForInStep β₂)}
    (hf : ∀ b₁ b₂, RB b₁ b₂ → Bisim ρ (LoopRel RB Ret) (f₁ () b₁) (f₂ () b₂))
    {b₁ : β₁} {b₂ : β₂} (h : RB b₁ b₂) :
    Bisim ρ Ret (forIn Lean.Loop.mk b₁ f₁) (forIn Lean.Loop.mk b₂ f₂) :=
  Bisim.iter RB (fun _ _ hb => Bisim.bind (hf _ _ hb) fun x y hxy => by
    cases x <;> cases y <;> simp only [LoopRel] at hxy <;> exact Bisim.pure hxy) h

theorem Bisim.forIn_list {α₁ α₂ β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) (φ : α₁ → α₂)
    {f₁ : α₁ → β₁ → CoFree E N (ForInStep β₁)} {f₂ : α₂ → β₂ → CoFree E N (ForInStep β₂)} :
    ∀ (l : List α₁),
    (∀ a ∈ l, ∀ b₁ b₂, RB b₁ b₂ → Bisim ρ (ForInRel RB) (f₁ a b₁) (f₂ (φ a) b₂)) →
    ∀ {b₁ : β₁} {b₂ : β₂}, RB b₁ b₂ → Bisim ρ RB (forIn l b₁ f₁) (forIn (l.map φ) b₂ f₂)
  | [], _, _, _, h => by
    rw [List.map_nil, List.forIn_nil, List.forIn_nil]; exact Bisim.pure h
  | a :: l, hf, _, _, h => by
    rw [List.map_cons, List.forIn_cons, List.forIn_cons]
    refine Bisim.bind (hf a (List.mem_cons_self ..) _ _ h) fun x y hxy => ?_
    cases x <;> cases y <;> simp only [ForInRel] at hxy
    · exact Bisim.pure hxy
    · exact Bisim.forIn_list RB φ l (fun a ha => hf a (List.mem_cons_of_mem _ ha)) hxy

theorem Bisim.forIn_array {α₁ α₂ β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) (φ : α₁ → α₂)
    {f₁ : α₁ → β₁ → CoFree E N (ForInStep β₁)} {f₂ : α₂ → β₂ → CoFree E N (ForInStep β₂)}
    (xs : Array α₁)
    (hf : ∀ a ∈ xs, ∀ b₁ b₂, RB b₁ b₂ → Bisim ρ (ForInRel RB) (f₁ a b₁) (f₂ (φ a) b₂))
    {b₁ : β₁} {b₂ : β₂} (h : RB b₁ b₂) : Bisim ρ RB (forIn xs b₁ f₁) (forIn (xs.map φ) b₂ f₂) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList, Array.toList_map]
  exact Bisim.forIn_list RB φ xs.toList (fun a ha => hf a (Array.mem_toList_iff.1 ha)) h

end Loops

section Fix

variable {I O : Type u} {ρ : OpRel E} {RI : I → I → Prop}
  {body₁ body₂ : I → CoFree (Effect.Call I O ⊕ₑ E) N O} {t₁ t₂ : CoFree (Effect.Call I O ⊕ₑ E) N O}

def Frames (ρ : OpRel E) (RI : I → I → Prop) :
    List (FixFrame body₁ t₁) → List (FixFrame body₂ t₂) → Prop
  | [], [] => True
  | fr₁ :: rest₁, fr₂ :: rest₂ =>
    (∀ o, Bisim (OpRel.calls RI ρ) Eq ((fixCode body₁ t₁ fr₁.code).atPos (fr₁.resume o))
      ((fixCode body₂ t₂ fr₂.code).atPos (fr₂.resume o))) ∧ Frames ρ RI rest₁ rest₂
  | _, _ => False

theorem Bisim.fixFrom
    (hbody : ∀ i₁ i₂, RI i₁ i₂ → Bisim (OpRel.calls RI ρ) Eq (body₁ i₁) (body₂ i₂))
    (ht : Bisim (OpRel.calls RI ρ) Eq t₁ t₂) :
    Bisim ρ Eq (CoFree.fixFrom body₁ t₁) (CoFree.fixFrom body₂ t₂) := by
  refine Bisim.coind (fun x y => ∃ c₁ p₁ st₁ c₂ p₂ st₂,
      x = (CoFree.fixFrom body₁ t₁).startAt ⟨c₁, p₁, st₁⟩ ∧ y = (CoFree.fixFrom body₂ t₂).startAt ⟨c₂, p₂, st₂⟩ ∧
      Bisim (OpRel.calls RI ρ) Eq ((fixCode body₁ t₁ c₁).atPos p₁) ((fixCode body₂ t₂ c₂).atPos p₂) ∧
      Frames ρ RI st₁ st₂)
    (fun x y ⟨c₁, p₁, st₁, c₂, p₂, st₂, hx, hy, hb, hst⟩ => ?_)
    ⟨none, t₁.initPos, [], none, t₂.initPos, [], rfl, rfl, by
      simp only [fixCode, atPos_initPos]; exact ht, trivial⟩
  subst hx hy
  rw [observe_fixFrom_startAt, observe_fixFrom_startAt]
  have hs := Bisim.unfold hb
  rw [observe_atPos, observe_atPos] at hs
  generalize (fixCode body₁ t₁ c₁).stepAt p₁ = s₁ at hs ⊢
  generalize (fixCode body₂ t₂ c₂).stepAt p₂ = s₂ at hs ⊢
  cases s₁ <;> cases s₂ <;> simp only [StepRel, Step.map] at hs
  · subst hs
    cases st₁ <;> cases st₂ <;> simp only [Frames] at hst
    · exact rfl
    · exact .inl ⟨_, _, _, _, _, _, rfl, rfl, hst.1 _, hst.2⟩
  · exact .inl ⟨_, _, _, _, _, _, rfl, rfl, hs, hst⟩
  · rename_i o₁ k₁ o₂ k₂
    rcases o₁ with i₁ | o₁ <;> rcases o₂ with i₂ | o₂
    · exact .inl ⟨_, _, _, _, _, _, rfl, rfl, by
        simp only [fixCode, atPos_initPos]; exact hbody _ _ hs.1, fun o => hs.2 o o rfl, hst⟩
    · exact (hs.1 : False).elim
    · exact (hs.1 : False).elim
    · exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, _, _, _, _, rfl, rfl, hs.2 r₁ r₂ hr, hst⟩⟩
  · exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, _, _, _, _, rfl, rfl, hs.2 r₁ r₂ hr, hst⟩⟩

theorem Bisim.fix
    {f₁ f₂ : (I → CoFree (Effect.Rec I O E) N O) → I → CoFree (Effect.Rec I O E) N O}
    (hbody : ∀ i₁ i₂, RI i₁ i₂ → Bisim (OpRel.calls RI ρ) Eq
      (f₁ (fun j => perform (E := Effect.Rec I O E) (.inl j)) i₁)
      (f₂ (fun j => perform (E := Effect.Rec I O E) (.inl j)) i₂))
    {i₁ i₂ : I} (hi : RI i₁ i₂) : Bisim ρ Eq (CoFree.fix f₁ i₁) (CoFree.fix f₂ i₂) :=
  Bisim.fixFrom hbody (hbody _ _ hi)

theorem Bisim.call {Ret : O → O → Prop} (hRet : ∀ o, Ret o o) {i₁ i₂ : I} (hi : RI i₁ i₂) :
    Bisim (OpRel.calls RI ρ) Ret (perform (E := Effect.Rec I O E) (N := N) (.inl i₁))
      (perform (E := Effect.Rec I O E) (.inl i₂)) := by
  refine Bisim.fold ⟨hi, fun r₁ r₂ hr => ?_⟩
  cases hr
  exact Bisim.pure (hRet _)

end Fix

section Interp

variable {σ : Type u}

theorem stepRel_map_diag {X : Type u} {R : CoFree F M B → CoFree F M B → Prop}
    {H₁ H₂ : X → CoFree F M B} (hH : ∀ x, R (H₁ x) (H₂ x)) (s : Step F M B X) :
    StepRel (OpRel.eq F) Eq R (s.map H₁) (s.map H₂) := by
  cases s with
  | pure b => exact rfl
  | silent x => exact hH x
  | impure o k => exact ⟨rfl, fun r₁ r₂ hr => by cases hr; exact hH _⟩
  | branch c k => exact ⟨rfl, fun r₁ r₂ hr => by cases hr; exact hH _⟩

theorem step_zip {X₁ X₂ : Type u} {P : X₁ → X₂ → Prop}
    {G₁ : X₁ → CoFree E N A} {G₂ : X₂ → CoFree E N A} {R : CoFree E N A → CoFree E N A → Prop}
    (hP : ∀ x₁ x₂, R (G₁ x₁) (G₂ x₂) → P x₁ x₂) :
    ∀ (s₁ : Step E N A X₁) (s₂ : Step E N A X₂),
      StepRel (OpRel.eq E) Eq R (s₁.map G₁) (s₂.map G₂) →
      ∃ z : Step E N A { q : X₁ × X₂ // P q.1 q.2 },
        z.map (fun q => q.1.1) = s₁ ∧ z.map (fun q => q.1.2) = s₂
  | .pure a, .pure b, h => by
    simp only [Step.map, StepRel] at h; subst h; exact ⟨.pure a, rfl, rfl⟩
  | .silent x₁, .silent x₂, h => ⟨.silent ⟨(x₁, x₂), hP _ _ h⟩, rfl, rfl⟩
  | .impure o₁ k₁, .impure o₂ k₂, h => by
    simp only [Step.map, StepRel, OpRel.eq] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨.impure o₁ fun r => ⟨(k₁ r, k₂ r), hP _ _ (h r r HEq.rfl)⟩, rfl, rfl⟩
  | .branch c₁ k₁, .branch c₂ k₂, h => by
    simp only [Step.map, StepRel] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨.branch c₁ fun r => ⟨(k₁ r, k₂ r), hP _ _ (h r r HEq.rfl)⟩, rfl, rfl⟩
  | .pure _, .silent _, h | .pure _, .impure .., h | .pure _, .branch .., h
  | .silent _, .pure _, h | .silent _, .impure .., h | .silent _, .branch .., h
  | .impure .., .pure _, h | .impure .., .silent _, h | .impure .., .branch .., h
  | .branch .., .pure _, h | .branch .., .silent _, h | .branch .., .impure .., h => h.elim

theorem Bisim.interp (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X))
    (hnat : ∀ {X Y : Type u} (st : σ) (s : Step E N A X) (f : X → Y),
      h st (s.map f) = (h st s).map fun q => (q.1, f q.2))
    {m₁ m₂ : CoFree E N A} (hm : Bisim (OpRel.eq E) Eq m₁ m₂) (st : σ) :
    Bisim (OpRel.eq F) Eq (CoFree.interp h st m₁) (CoFree.interp h st m₂) := by
  refine Bisim.coind (fun x y => ∃ st n₁ n₂, Bisim (OpRel.eq E) Eq n₁ n₂ ∧
      x = CoFree.interp h st n₁ ∧ y = CoFree.interp h st n₂)
    (fun x y ⟨st, n₁, n₂, hn, hx, hy⟩ => ?_) ⟨st, m₁, m₂, hm, rfl, rfl⟩
  subst hx hy
  have hs := Bisim.unfold hn
  unfold observe at hs
  obtain ⟨z, hz₁, hz₂⟩ := step_zip (P := fun x₁ x₂ => Bisim (OpRel.eq E) Eq (n₁.next x₁) (n₂.next x₂))
    (fun _ _ h => h) _ _ hs
  have e₁ : (CoFree.interp h st n₁).observe = (h st z).map fun q => CoFree.interp h q.1 (n₁.next q.2.1.1) := by
    rw [observe_interp, ← hz₁, hnat, Step.map_map]
    exact Step.map_congr (by rintro ⟨_, ⟨⟨_ | _, _⟩, _⟩⟩ <;> rfl) _
  have e₂ : (CoFree.interp h st n₂).observe = (h st z).map fun q => CoFree.interp h q.1 (n₂.next q.2.1.2) := by
    rw [observe_interp, ← hz₂, hnat, Step.map_map]
    exact Step.map_congr (by rintro ⟨_, ⟨⟨_, _ | _⟩, _⟩⟩ <;> rfl) _
  rw [e₁, e₂]
  exact stepRel_map_diag (fun q => .inl ⟨q.1, _, _, q.2.2, rfl, rfl⟩) _

end Interp

section Same

variable {N₁ : NonDeterminism.{u}} {Ret : A → B → Prop}

theorem Same.bisim {x : CoFree E N₁ A} {y z : CoFree E N B} (hxy : Same Ret x y)
    (hyz : Bisim (OpRel.eq E) Eq y z) : Same Ret x z := by
  refine Same.coind (fun x z => ∃ y, Same Ret x y ∧ Bisim (OpRel.eq E) Eq y z)
    (fun x z hxz => ?_) ⟨y, hxy, hyz⟩
  obtain ⟨y, hxy, hyz⟩ := hxz
  have hf := Same.unfold hxy
  clear hxy
  induction hf generalizing z with
  | ret a b hx hy hab =>
    have hs := Bisim.unfold hyz
    rw [hy] at hs
    generalize hz : z.observe = sz at hs
    cases sz <;> simp only [StepRel] at hs
    subst hs
    exact .ret a b hx hz hab
  | impure op hx hy hc =>
    have hs := Bisim.unfold hyz
    rw [hy] at hs
    generalize hz : z.observe = sz at hs
    cases sz <;> simp only [StepRel, OpRel.eq] at hs
    obtain ⟨rfl, hk⟩ := hs
    exact .impure op hx hz fun r => .inl ⟨_, hc r, hk r r HEq.rfl⟩
  | silentL hx _ ih => exact .silentL hx (ih _ hyz)
  | silentR hy _ ih =>
    have hs := Bisim.unfold hyz
    rw [hy] at hs
    generalize hz : z.observe = sz at hs
    cases sz <;> simp only [StepRel] at hs
    exact .silentR hz (ih _ hs)
  | branchL op hx _ ih => exact .branchL op hx fun r => ih r _ hyz
  | branchR op hy _ ih =>
    have hs := Bisim.unfold hyz
    rw [hy] at hs
    generalize hz : z.observe = sz at hs
    cases sz <;> simp only [StepRel] at hs
    obtain ⟨rfl, hk⟩ := hs
    exact .branchR op hz fun r => ih r _ (hk r r HEq.rfl)
  | @mutualUnobservedStep x y hu =>
    refine .mutualUnobservedStep (forallUnobserved_mono hu fun x' hy => ?_)
    have hs := Bisim.unfold hyz
    unfold ForallUnobserved at hy ⊢
    generalize y.observe = sy at hy hs
    generalize z.observe = sz at hs ⊢
    cases sy <;> cases sz <;> simp only [StepRel] at hs hy ⊢
    · exact .inl ⟨_, hy, hs⟩
    · obtain ⟨rfl, hk⟩ := hs
      exact fun r => .inl ⟨_, hy r, hk r r HEq.rfl⟩

theorem Bisim.same {x y : CoFree E N A} {z : CoFree E N₁ B} (hxy : Bisim (OpRel.eq E) Eq x y)
    (hyz : Same Ret y z) : Same Ret x z :=
  Same.symm (Same.bisim (Same.symm hyz) (Bisim.symm hxy))

theorem Deterministic.bisim {x y : CoFree E N A} (hx : Deterministic x)
    (hxy : Bisim (OpRel.eq E) Eq x y) : Deterministic y :=
  Bisim.same (Bisim.symm hxy) (Same.bisim hx hxy)

theorem HasOutcome.bisim {m₁ m₂ : CoFree E N A} {o : Outcome E A} (h : HasOutcome m₁ o)
    (hb : Bisim (OpRel.eq E) Eq m₁ m₂) : HasOutcome m₂ o := by
  induction h generalizing m₂ with
  | res hv =>
    have hs := Bisim.unfold hb
    rw [hv] at hs
    generalize hz : m₂.observe = sz at hs
    cases sz <;> simp only [StepRel] at hs
    subst hs
    exact .res hz
  | terminal hr hk =>
    obtain ⟨k, hk⟩ := hk
    have hs := Bisim.unfold hb
    rw [hk] at hs
    generalize hz : m₂.observe = sz at hs
    cases sz <;> simp only [StepRel, OpRel.eq] at hs
    obtain ⟨rfl, _⟩ := hs
    exact .terminal hr ⟨_, hz⟩
  | silent _ hm ih =>
    have hs := Bisim.unfold hb
    rw [hm] at hs
    generalize hz : m₂.observe = sz at hs
    cases sz <;> simp only [StepRel] at hs
    exact .silent (ih hs) hz
  | branch _ hm ih =>
    obtain ⟨br, k, hm, r, rfl⟩ := hm
    have hs := Bisim.unfold hb
    rw [hm] at hs
    generalize hz : m₂.observe = sz at hs
    cases sz <;> simp only [StepRel] at hs
    obtain ⟨rfl, hk⟩ := hs
    exact .branch (ih (hk r r HEq.rfl)) ⟨_, _, hz, r, rfl⟩
  | impure _ hm ih =>
    obtain ⟨op, k, hm, r, rfl⟩ := hm
    have hs := Bisim.unfold hb
    rw [hm] at hs
    generalize hz : m₂.observe = sz at hs
    cases sz <;> simp only [StepRel, OpRel.eq] at hs
    obtain ⟨rfl, hk⟩ := hs
    exact .impure (ih (hk r r HEq.rfl)) ⟨_, _, hz, r, rfl⟩

end Same

end CoFree.Proofs
