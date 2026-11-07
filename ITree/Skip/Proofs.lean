import ITree.Skip
import ITree.Bisim.Theorems
import ITree.Same.Theorems
import ITree.Machine.Theorems
import ITree.Reaches.Theorems

universe u

namespace CoFree.Proofs

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A B C D : Type u}

section Basic

variable {ex : E.Op → Prop} {bad : A → Prop} {Ret : A → B → Prop}

lemma skipFinite_mono {R R' : CoFree E N A → CoFree E N B → Prop} (hR : ∀ x y, R x y → R' x y)
    {m₁ : CoFree E N A} {m₂ : CoFree E N B} (h : SkipFinite ex bad Ret R m₁ m₂) :
    SkipFinite ex bad Ret R' m₁ m₂ := by
  induction h with
  | step hs => exact .step (stepRel_mono hR hs)
  | silentL h₁ _ ih => exact .silentL h₁ ih
  | extraL op h₁ hx _ ih => exact .extraL op h₁ hx ih
  | badL a h₁ hb => exact .badL a h₁ hb

lemma skipFinite_congr {R : CoFree E N A → CoFree E N B → Prop}
    {m₁ m₁' : CoFree E N A} {m₂ m₂' : CoFree E N B} (h : SkipFinite ex bad Ret R m₁ m₂)
    (he₁ : m₁.observe = m₁'.observe) (he₂ : m₂.observe = m₂'.observe) :
    SkipFinite ex bad Ret R m₁' m₂' := by
  induction h generalizing m₁' with
  | step hs => exact .step (he₁ ▸ he₂ ▸ hs)
  | silentL h₁ _ ih => exact .silentL (he₁ ▸ h₁) (ih rfl he₂)
  | extraL op h₁ hx _ ih => exact .extraL op (he₁ ▸ h₁) hx fun r => ih r rfl he₂
  | badL a h₁ hb => exact .badL a (he₁ ▸ h₁) hb

lemma Skip.unfold {m₁ : CoFree E N A} {m₂ : CoFree E N B} (h : Skip ex bad Ret m₁ m₂) :
    SkipFinite ex bad Ret (Skip ex bad Ret) m₁ m₂ := by
  obtain ⟨R, hm, hR⟩ := h
  exact skipFinite_mono (fun x y hxy => ⟨R, hxy, hR⟩) (hR _ _ hm)

lemma Skip.coind (R : CoFree E N A → CoFree E N B → Prop)
    (hR : ∀ x y, R x y → SkipFinite ex bad Ret (fun a b => R a b ∨ Skip ex bad Ret a b) x y)
    {m₁ : CoFree E N A} {m₂ : CoFree E N B} (h : R m₁ m₂) : Skip ex bad Ret m₁ m₂ := by
  refine ⟨fun a b => R a b ∨ Skip ex bad Ret a b, .inl h, fun x y hxy => ?_⟩
  rcases hxy with hxy | hxy
  · exact hR x y hxy
  · exact skipFinite_mono (fun _ _ => .inr) (Skip.unfold hxy)

lemma Skip.fold {m₁ : CoFree E N A} {m₂ : CoFree E N B}
    (h : SkipFinite ex bad Ret (Skip ex bad Ret) m₁ m₂) : Skip ex bad Ret m₁ m₂ :=
  Skip.coind (fun x y => x = m₁ ∧ y = m₂)
    (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact skipFinite_mono (fun _ _ => .inr) h) ⟨rfl, rfl⟩

lemma Skip.congr {m₁ m₁' : CoFree E N A} {m₂ m₂' : CoFree E N B}
    (he₁ : m₁.observe = m₁'.observe) (he₂ : m₂.observe = m₂'.observe)
    (h : Skip ex bad Ret m₁ m₂) : Skip ex bad Ret m₁' m₂' :=
  Skip.fold (skipFinite_congr (Skip.unfold h) he₁ he₂)

lemma Skip.of_bisim {m₁ : CoFree E N A} {m₂ : CoFree E N B}
    (h : Bisim (OpRel.eq E) Ret m₁ m₂) : Skip ex bad Ret m₁ m₂ :=
  Skip.coind (Bisim (OpRel.eq E) Ret) (fun _ _ h => .step (stepRel_mono (fun _ _ => .inl)
    (Bisim.unfold h))) h

lemma Skip.mono {ex' : E.Op → Prop} {bad' : A → Prop} {Ret' : A → B → Prop}
    (hex : ∀ o, ex o → ex' o) (hbad : ∀ a, bad a → bad' a) (hRet : ∀ a b, Ret a b → Ret' a b)
    {m₁ : CoFree E N A} {m₂ : CoFree E N B} (h : Skip ex bad Ret m₁ m₂) :
    Skip ex' bad' Ret' m₁ m₂ := by
  refine Skip.coind (Skip ex bad Ret) (fun x y hxy => ?_) h
  have hf := Skip.unfold hxy
  clear hxy
  induction hf with
  | step hs => exact .step (stepRel_mono_ret hRet (stepRel_mono (fun _ _ => .inl) hs))
  | silentL h₁ _ ih => exact .silentL h₁ ih
  | extraL op h₁ hx _ ih => exact .extraL op h₁ (hex _ hx) ih
  | badL a h₁ hb => exact .badL a h₁ (hbad _ hb)

lemma Skip.pure {a : A} {b : B} (h : Ret a b) :
    Skip ex bad Ret (CoFree.pure a : CoFree E N A) (CoFree.pure b) :=
  Skip.of_bisim (Bisim.pure h)

lemma Skip.extra {op : E.Op} {k : E.Resp op → CoFree E N A} {m₁ : CoFree E N A}
    {m₂ : CoFree E N B} (h₁ : m₁.observe = .impure op k) (hx : ex op)
    (h : ∀ r, Skip ex bad Ret (k r) m₂) : Skip ex bad Ret m₁ m₂ :=
  Skip.fold (.extraL op h₁ hx fun r => Skip.unfold (h r))

end Basic

section Bind

variable {ex : E.Op → Prop} {bad : A → Prop} {Ret : A → B → Prop}

lemma Skip.bind {bad' : C → Prop} {Ret' : C → D → Prop} {m₁ : CoFree E N A}
    {m₂ : CoFree E N B} {g₁ : A → CoFree E N C} {g₂ : B → CoFree E N D}
    (h : Skip ex bad Ret m₁ m₂) (hg : ∀ a b, Ret a b → Skip ex bad' Ret' (g₁ a) (g₂ b))
    (hbad : ∀ a, bad a → ∃ c, (g₁ a).observe = .pure c ∧ bad' c) :
    Skip ex bad' Ret' (m₁.bind g₁) (m₂.bind g₂) := by
  refine Skip.coind (fun x y => ∃ n₁ n₂, Skip ex bad Ret n₁ n₂ ∧ x = n₁.bind g₁ ∧ y = n₂.bind g₂)
    (fun x y hxy => ?_) ⟨m₁, m₂, h, rfl, rfl⟩
  obtain ⟨n₁, n₂, hn, rfl, rfl⟩ := hxy
  have hf := Skip.unfold hn
  clear hn
  induction hf with
  | @step n₁ n₂ hs =>
    have e₁ := observe_bind n₁ g₁
    have e₂ := observe_bind n₂ g₂
    generalize n₁.observe = s₁ at hs e₁
    generalize n₂.observe = s₂ at hs e₂
    cases s₁ <;> cases s₂ <;> simp only [StepRel] at hs
    · exact skipFinite_congr (skipFinite_mono (fun _ _ => .inr) (Skip.unfold (hg _ _ hs)))
        e₁.symm e₂.symm
    · exact .step (by rw [e₁, e₂]; exact .inl ⟨_, _, hs, rfl, rfl⟩)
    · exact .step (by rw [e₁, e₂]; exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, hs.2 r₁ r₂ hr, rfl, rfl⟩⟩)
    · exact .step (by rw [e₁, e₂]; exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, hs.2 r₁ r₂ hr, rfl, rfl⟩⟩)
  | silentL h₁ _ ih =>
    exact .silentL (by rw [observe_bind, h₁]; rfl) ih
  | extraL op h₁ hx _ ih =>
    exact .extraL op (by rw [observe_bind, h₁]; rfl) hx ih
  | badL a h₁ hb =>
    obtain ⟨c, hc, hb'⟩ := hbad a hb
    exact .badL c (by rw [observe_bind, h₁]; exact hc) hb'

lemma Skip.mapOps {ex' : F.Op → Prop} (e : Effect.Map E F) (nd : NonDeterminism.Map N M)
    (hex : ∀ o, ex o → ex' (e.op o)) {m₁ : CoFree E N A} {m₂ : CoFree E N B}
    (h : Skip ex bad Ret m₁ m₂) : Skip ex' bad Ret (m₁.mapOps e nd) (m₂.mapOps e nd) := by
  refine Skip.coind (fun x y => ∃ n₁ n₂, Skip ex bad Ret n₁ n₂ ∧ x = n₁.mapOps e nd ∧
      y = n₂.mapOps e nd) (fun x y hxy => ?_) ⟨m₁, m₂, h, rfl, rfl⟩
  obtain ⟨n₁, n₂, hn, rfl, rfl⟩ := hxy
  have hf := Skip.unfold hn
  clear hn
  induction hf with
  | @step n₁ n₂ hs =>
    have e₁ := observe_mapOps e nd n₁
    have e₂ := observe_mapOps e nd n₂
    generalize n₁.observe = s₁ at hs e₁
    generalize n₂.observe = s₂ at hs e₂
    refine .step ?_
    rw [e₁, e₂]
    cases s₁ <;> cases s₂ <;> simp only [StepRel, OpRel.eq] at hs ⊢
    · exact hs
    · exact .inl ⟨_, _, hs, rfl, rfl⟩
    · obtain ⟨rfl, hk⟩ := hs
      exact ⟨rfl, fun r₁ r₂ hr => by cases hr; exact .inl ⟨_, _, hk _ _ HEq.rfl, rfl, rfl⟩⟩
    · obtain ⟨rfl, hk⟩ := hs
      exact ⟨rfl, fun r₁ r₂ hr => by cases hr; exact .inl ⟨_, _, hk _ _ HEq.rfl, rfl, rfl⟩⟩
  | silentL h₁ _ ih =>
    exact .silentL (by rw [observe_mapOps, h₁]) ih
  | extraL op h₁ hx _ ih =>
    exact .extraL (e.op op) (by rw [observe_mapOps, h₁]) (hex _ hx) fun r => ih _
  | badL a h₁ hb => exact .badL a (by rw [observe_mapOps, h₁]) hb

lemma Skip.prefix {P : A → Prop} {bad' : C → Prop} {Ret' : C → D → Prop} {m : CoFree E N A}
    {g : A → CoFree E N C} {n : CoFree E N D}
    (hm : Skip ex (fun _ => False) (fun a (_ : PUnit) => P a) m (CoFree.pure ⟨⟩))
    (hg : ∀ a, P a → Skip ex bad' Ret' (g a) n) : Skip ex bad' Ret' (m.bind g) n :=
  Skip.congr rfl (by rw [observe_bind, observe_pure]; rfl)
    (Skip.bind (g₂ := fun _ => n) hm (fun a _ h => hg a h) nofun)

end Bind

section Loops

variable {ex : E.Op → Prop} {S₁ S₂ : Type u}

lemma Skip.iter {Ret : A → B → Prop} (RS : S₁ → S₂ → Prop)
    {g₁ : S₁ → CoFree E N (IterStep S₁ A)} {g₂ : S₂ → CoFree E N (IterStep S₂ B)}
    (hg : ∀ s₁ s₂, RS s₁ s₂ → Skip ex (fun _ => False) (IterRel RS Ret) (g₁ s₁) (g₂ s₂))
    {s₁ : S₁} {s₂ : S₂} (h : RS s₁ s₂) :
    Skip ex (fun _ => False) Ret (CoFree.iter s₁ g₁) (CoFree.iter s₂ g₂) := by
  refine Skip.coind (fun x y => ∃ i₁ p₁ i₂ p₂, x = (CoFree.iter s₁ g₁).startAt ⟨i₁, p₁⟩ ∧
      y = (CoFree.iter s₂ g₂).startAt ⟨i₂, p₂⟩ ∧
      Skip ex (fun _ => False) (IterRel RS Ret) ((g₁ i₁).atPos p₁) ((g₂ i₂).atPos p₂))
    (fun x y hxy => ?_)
    ⟨s₁, (g₁ s₁).initPos, s₂, (g₂ s₂).initPos, rfl, rfl, by
      rw [atPos_initPos, atPos_initPos]; exact hg _ _ h⟩
  obtain ⟨i₁, p₁, i₂, p₂, rfl, rfl, hb⟩ := hxy
  have hf := Skip.unfold hb
  clear hb
  generalize hm : (g₁ i₁).atPos p₁ = m at hf
  generalize hm₂ : (g₂ i₂).atPos p₂ = m₂ at hf
  induction hf generalizing p₁ with
  | @step m₁ m₂ hs =>
    subst hm hm₂
    refine .step ?_
    rw [observe_iter_startAt, observe_iter_startAt]
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
  | silentL h₁ _ ih =>
    subst hm
    rw [observe_atPos] at h₁
    generalize hst : (g₁ i₁).stepAt p₁ = st at h₁
    cases st <;> simp only [Step.map, Step.silent.injEq, reduceCtorEq] at h₁
    rename_i p'
    subst h₁
    exact .silentL (by rw [observe_iter_startAt, hst]) (ih p' rfl hm₂)
  | extraL op h₁ hx _ ih =>
    subst hm
    rw [observe_atPos] at h₁
    generalize hst : (g₁ i₁).stepAt p₁ = st at h₁
    cases st <;> simp only [Step.map, Step.impure.injEq, reduceCtorEq] at h₁
    rename_i op' k'
    obtain ⟨rfl, h₁⟩ := h₁
    cases h₁
    exact .extraL _ (by rw [observe_iter_startAt, hst]) hx
      fun r => ih r (k' r) rfl hm₂
  | badL a h₁ hb => exact hb.elim

lemma Skip.loop {β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) {Ret : β₁ → β₂ → Prop}
    {f₁ : Unit → β₁ → CoFree E N (ForInStep β₁)} {f₂ : Unit → β₂ → CoFree E N (ForInStep β₂)}
    (hf : ∀ b₁ b₂, RB b₁ b₂ → Skip ex (fun _ => False) (LoopRel RB Ret) (f₁ () b₁) (f₂ () b₂))
    {b₁ : β₁} {b₂ : β₂} (h : RB b₁ b₂) :
    Skip ex (fun _ => False) Ret (forIn Lean.Loop.mk b₁ f₁) (forIn Lean.Loop.mk b₂ f₂) :=
  Skip.iter RB (fun _ _ hb => Skip.bind (hf _ _ hb) (fun x y hxy => by
    cases x <;> cases y <;> simp only [LoopRel] at hxy <;> exact Skip.pure hxy) nofun) h

lemma Skip.forIn_list_filter {α β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) (keep : α → Bool)
    {f₁ : α → β₁ → CoFree E N (ForInStep β₁)} {f₂ : α → β₂ → CoFree E N (ForInStep β₂)} :
    ∀ (l : List α),
    (∀ a ∈ l, keep a → ∀ b₁ b₂, RB b₁ b₂ →
      Skip ex (fun _ => False) (ForInRel RB) (f₁ a b₁) (f₂ a b₂)) →
    (∀ a ∈ l, keep a = false → ∀ b₁ b₂, RB b₁ b₂ →
      Skip ex (fun _ => False) (ForInRel RB) (f₁ a b₁) (CoFree.pure (.yield b₂))) →
    ∀ {b₁ : β₁} {b₂ : β₂}, RB b₁ b₂ →
      Skip ex (fun _ => False) RB (forIn l b₁ f₁) (forIn (l.filter keep) b₂ f₂)
  | [], _, _, _, _, h => by
    rw [List.filter_nil, List.forIn_nil, List.forIn_nil]; exact Skip.pure h
  | a :: l, hk, hd, b₁, b₂, h => by
    have ih : ∀ {b₁ b₂}, RB b₁ b₂ → _ := fun {b₁ b₂} => Skip.forIn_list_filter RB keep l
      (fun a ha => hk a (List.mem_cons_of_mem _ ha)) (fun a ha => hd a (List.mem_cons_of_mem _ ha))
      (b₁ := b₁) (b₂ := b₂)
    rw [List.forIn_cons, List.filter_cons]
    cases hka : keep a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hb := Skip.bind (g₁ := fun
          | ForInStep.done b => CoFree.pure b
          | ForInStep.yield b => forIn l b f₁) (g₂ := fun
          | ForInStep.done b => CoFree.pure b
          | ForInStep.yield b => forIn (l.filter keep) b f₂) (Ret' := RB) (bad' := fun _ => False)
        (hd a (List.mem_cons_self ..) hka _ _ h) (fun x y hxy => by
          cases x <;> cases y <;> simp only [ForInRel] at hxy
          · exact Skip.pure hxy
          · exact ih hxy) nofun
      exact Skip.congr rfl (by rw [observe_bind, observe_pure]; rfl) hb
    · simp only [↓reduceIte, List.forIn_cons]
      refine Skip.bind (hk a (List.mem_cons_self ..) hka _ _ h) (fun x y hxy => ?_) nofun
      cases x <;> cases y <;> simp only [ForInRel] at hxy
      · exact Skip.pure hxy
      · exact ih hxy

lemma Skip.forIn_array_filter {α β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) (keep : α → Bool)
    {f₁ : α → β₁ → CoFree E N (ForInStep β₁)} {f₂ : α → β₂ → CoFree E N (ForInStep β₂)}
    (xs : Array α)
    (hk : ∀ a ∈ xs, keep a → ∀ b₁ b₂, RB b₁ b₂ →
      Skip ex (fun _ => False) (ForInRel RB) (f₁ a b₁) (f₂ a b₂))
    (hd : ∀ a ∈ xs, keep a = false → ∀ b₁ b₂, RB b₁ b₂ →
      Skip ex (fun _ => False) (ForInRel RB) (f₁ a b₁) (CoFree.pure (.yield b₂)))
    {b₁ : β₁} {b₂ : β₂} (h : RB b₁ b₂) :
    Skip ex (fun _ => False) RB (forIn xs b₁ f₁) (forIn (xs.filter keep) b₂ f₂) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList, Array.toList_filter]
  exact Skip.forIn_list_filter RB keep xs.toList (fun a ha => hk a (Array.mem_toList_iff.1 ha))
    (fun a ha => hd a (Array.mem_toList_iff.1 ha)) h

end Loops

section Fix

variable {I O : Type u} {ex : E.Op → Prop}
  {body₁ body₂ : I → CoFree (Effect.Call I O ⊕ₑ E) N O} {t₁ t₂ : CoFree (Effect.Call I O ⊕ₑ E) N O}

def SkipFrames (ex : E.Op → Prop) : List (FixFrame body₁ t₁) → List (FixFrame body₂ t₂) → Prop
  | [], [] => True
  | fr₁ :: rest₁, fr₂ :: rest₂ =>
    (∀ o, Skip (recExtra ex) (fun _ => False) Eq ((fixCode body₁ t₁ fr₁.code).atPos (fr₁.resume o))
      ((fixCode body₂ t₂ fr₂.code).atPos (fr₂.resume o))) ∧ SkipFrames ex rest₁ rest₂
  | _, _ => False

lemma Skip.fixFrom
    (hbody : ∀ i, Skip (recExtra ex) (fun _ => False) Eq (body₁ i) (body₂ i))
    (ht : Skip (recExtra ex) (fun _ => False) Eq t₁ t₂) :
    Skip ex (fun _ => False) Eq (CoFree.fixFrom body₁ t₁) (CoFree.fixFrom body₂ t₂) := by
  refine Skip.coind (fun x y => ∃ c₁ p₁ st₁ c₂ p₂ st₂,
      x = (CoFree.fixFrom body₁ t₁).startAt ⟨c₁, p₁, st₁⟩ ∧
      y = (CoFree.fixFrom body₂ t₂).startAt ⟨c₂, p₂, st₂⟩ ∧
      Skip (recExtra ex) (fun _ => False) Eq ((fixCode body₁ t₁ c₁).atPos p₁)
        ((fixCode body₂ t₂ c₂).atPos p₂) ∧
      SkipFrames ex st₁ st₂)
    (fun x y hxy => ?_)
    ⟨none, t₁.initPos, [], none, t₂.initPos, [], rfl, rfl, by
      simp only [fixCode, atPos_initPos]; exact ht, trivial⟩
  obtain ⟨c₁, p₁, st₁, c₂, p₂, st₂, rfl, rfl, hb, hst⟩ := hxy
  have hf := Skip.unfold hb
  clear hb
  generalize hm : (fixCode body₁ t₁ c₁).atPos p₁ = m at hf
  generalize hm₂ : (fixCode body₂ t₂ c₂).atPos p₂ = m₂ at hf
  induction hf generalizing p₁ with
  | @step m₁ m₂ hs =>
    subst hm hm₂
    refine .step ?_
    rw [observe_fixFrom_startAt, observe_fixFrom_startAt]
    rw [observe_atPos, observe_atPos] at hs
    generalize (fixCode body₁ t₁ c₁).stepAt p₁ = s₁ at hs ⊢
    generalize (fixCode body₂ t₂ c₂).stepAt p₂ = s₂ at hs ⊢
    cases s₁ <;> cases s₂ <;> simp only [StepRel, Step.map] at hs
    · subst hs
      cases st₁ <;> cases st₂ <;> simp only [SkipFrames] at hst
      · exact rfl
      · exact .inl ⟨_, _, _, _, _, _, rfl, rfl, hst.1 _, hst.2⟩
    · exact .inl ⟨_, _, _, _, _, _, rfl, rfl, hs, hst⟩
    · rename_i o₁ k₁ o₂ k₂
      obtain ⟨heq, hk⟩ := hs
      cases heq
      rcases o₁ with i | o
      · exact .inl ⟨_, _, _, _, _, _, rfl, rfl, by
          simp only [fixCode, atPos_initPos]; exact hbody i, fun o => hk o o HEq.rfl, hst⟩
      · exact ⟨rfl, fun r₁ r₂ hr => .inl ⟨_, _, _, _, _, _, rfl, rfl, hk r₁ r₂ hr, hst⟩⟩
    · exact ⟨hs.1, fun r₁ r₂ hr => .inl ⟨_, _, _, _, _, _, rfl, rfl, hs.2 r₁ r₂ hr, hst⟩⟩
  | silentL h₁ _ ih =>
    subst hm
    rw [observe_atPos] at h₁
    generalize hs : (fixCode body₁ t₁ c₁).stepAt p₁ = s at h₁
    cases s <;> simp only [Step.map, Step.silent.injEq, reduceCtorEq] at h₁
    rename_i p'
    subst h₁
    exact .silentL (by rw [observe_fixFrom_startAt, hs]) (ih p' rfl hm₂)
  | extraL op h₁ hx _ ih =>
    subst hm
    rw [observe_atPos] at h₁
    generalize hs : (fixCode body₁ t₁ c₁).stepAt p₁ = s at h₁
    cases s <;> simp only [Step.map, Step.impure.injEq, reduceCtorEq] at h₁
    rename_i op' k'
    obtain ⟨rfl, h₁⟩ := h₁
    cases h₁
    rcases op' with i | o
    · exact hx.elim
    · exact .extraL o (by rw [observe_fixFrom_startAt, hs]) hx fun r => ih r (k' r) rfl hm₂
  | badL a h₁ hb => exact hb.elim

lemma Skip.fix {f₁ f₂ : (I → CoFree (Effect.Rec I O E) N O) → I → CoFree (Effect.Rec I O E) N O}
    (hbody : ∀ i, Skip (recExtra ex) (fun _ => False) Eq
      (f₁ (fun j => perform (E := Effect.Rec I O E) (.inl j)) i)
      (f₂ (fun j => perform (E := Effect.Rec I O E) (.inl j)) i)) (i : I) :
    Skip ex (fun _ => False) Eq (CoFree.fix f₁ i) (CoFree.fix f₂ i) :=
  Skip.fixFrom hbody (hbody i)

end Fix

section Interp

variable {σ : Type u}

lemma interp_obs (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X)) (st : σ)
    (m : CoFree E N A) :
    (CoFree.interp h st m).observe = (h st (m.step m.initial)).map fun q =>
      CoFree.interp h q.1 (m.next q.2) := by
  rw [observe_interp]
  exact Step.map_congr (by rintro ⟨_, _ | _⟩ <;> rfl) _

lemma Skip.interp (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X))
    (hnat : ∀ {X Y : Type u} (st : σ) (s : Step E N A X) (f : X → Y),
      h st (s.map f) = (h st s).map fun q => (q.1, f q.2))
    {ex : E.Op → Prop} {bad : A → Prop} {ex' : F.Op → Prop} {bad' : B → Prop}
    (hsilent : ∀ {X : Type u} (st : σ) (x : X), h st (.silent x) = .silent (st, x))
    (hextra : ∀ (st : σ) (op : E.Op), ex op →
      HandledExtra ex' bad' st (h st (.impure op fun r => r)))
    (hbad : ∀ {X : Type u} (st : σ) (a : A), bad a →
      ∃ b, h (X := X) st (.pure a) = .pure b ∧ bad' b)
    {m₁ m₂ : CoFree E N A} (hm : Skip ex bad Eq m₁ m₂) (st : σ) :
    Skip ex' bad' Eq (CoFree.interp h st m₁) (CoFree.interp h st m₂) := by
  refine Skip.coind (fun x y => ∃ st n₁ n₂, Skip ex bad Eq n₁ n₂ ∧
      x = CoFree.interp h st n₁ ∧ y = CoFree.interp h st n₂)
    (fun x y hxy => ?_) ⟨st, m₁, m₂, hm, rfl, rfl⟩
  obtain ⟨st, n₁, n₂, hn, rfl, rfl⟩ := hxy
  have hf := Skip.unfold hn
  clear hn
  induction hf generalizing st with
  | @step n₁ n₂ hs =>
    unfold observe at hs
    obtain ⟨z, hz₁, hz₂⟩ := step_zip
      (P := fun x₁ x₂ => Skip ex bad Eq (n₁.next x₁) (n₂.next x₂)) (fun _ _ h => h) _ _ hs
    have e₁ : (CoFree.interp h st n₁).observe =
        (h st z).map fun q => CoFree.interp h q.1 (n₁.next q.2.1.1) := by
      rw [observe_interp, ← hz₁, hnat, Step.map_map]
      exact Step.map_congr (by rintro ⟨_, ⟨⟨_ | _, _⟩, _⟩⟩ <;> rfl) _
    have e₂ : (CoFree.interp h st n₂).observe =
        (h st z).map fun q => CoFree.interp h q.1 (n₂.next q.2.1.2) := by
      rw [observe_interp, ← hz₂, hnat, Step.map_map]
      exact Step.map_congr (by rintro ⟨_, ⟨⟨_, _ | _⟩, _⟩⟩ <;> rfl) _
    refine .step ?_
    rw [e₁, e₂]
    exact stepRel_map_diag (fun q => .inl ⟨q.1, _, _, q.2.2, rfl, rfl⟩) _
  | @silentL n₁ n₁' _ h₁ _ ih =>
    unfold observe at h₁
    generalize hs : n₁.step n₁.initial = s at h₁
    cases s <;> simp only [Step.map, Step.silent.injEq, reduceCtorEq] at h₁
    subst h₁
    exact .silentL (by rw [interp_obs, hs, hsilent]; rfl) (ih st)
  | @extraL n₁ _ op k h₁ hx _ ih =>
    unfold observe at h₁
    generalize hs : n₁.step n₁.initial = s at h₁
    cases s <;> simp only [Step.map, Step.impure.injEq, reduceCtorEq] at h₁
    rename_i op₀ k₀
    obtain ⟨hop, h₁⟩ := h₁
    subst hop
    cases h₁
    have e : (CoFree.interp h st n₁).observe = (h st (.impure op₀ fun r => r)).map
        fun q => CoFree.interp h q.1 (n₁.next (k₀ q.2)) := by
      rw [interp_obs, hs]
      exact (congrArg (Step.map _) (hnat st (.impure op₀ fun r => r) k₀)).trans (Step.map_map _ _ _)
    have hh := hextra st op₀ hx
    generalize h st (.impure op₀ fun r => r) = s at e hh
    rcases s with b | ⟨st', r⟩ | ⟨op', k'⟩ | _
    · exact .badL b e hh
    · simp only [HandledExtra] at hh
      subst hh
      exact .silentL e (ih r st')
    · obtain ⟨hx', hk'⟩ := hh
      refine .extraL op' e hx' fun r' => ?_
      simp only [Function.comp_apply]
      rw [hk' r']
      exact ih _ st
    · exact hh.elim
  | @badL n₁ _ a h₁ hb =>
    unfold observe at h₁
    generalize hs : n₁.step n₁.initial = s at h₁
    cases s <;> simp only [Step.map, Step.pure.injEq, reduceCtorEq] at h₁
    rename_i a₀
    subst h₁
    obtain ⟨b, hb', hbb⟩ := hbad st a₀ hb
    exact .badL b (by rw [interp_obs, hs, hb']; rfl) hbb

end Interp

section Same

variable {N₁ : NonDeterminism.{u}} {Ret : A → B → Prop} {bad : B → Prop}

lemma noBad_silent {m m' : CoFree E N B} (h : NoBad bad m) (hm : m.observe = .silent m') :
    NoBad bad m' :=
  fun b hb ho => h b hb (.silent ho hm)

lemma noBad_branch {m : CoFree E N B} {c : N.Op} {k : N.Resp c → CoFree E N B}
    (h : NoBad bad m) (hm : m.observe = .branch c k) (r : N.Resp c) : NoBad bad (k r) :=
  fun b hb ho => h b hb (.branch ho ⟨c, k, hm, r, rfl⟩)

lemma noBad_impure {m : CoFree E N B} {op : E.Op} {k : E.Resp op → CoFree E N B}
    (h : NoBad bad m) (hm : m.observe = .impure op k) (r : E.Resp op) : NoBad bad (k r) :=
  fun b hb ho => h b hb (.impure ho ⟨op, k, hm, r, rfl⟩)

lemma skip_peel {P : CoFree E N B → Prop} {y z : CoFree E N B}
    (hyz : Skip (fun _ => False) bad Eq y z) (hy : NoBad bad y)
    (hsil : ∀ y y', y.observe = .silent y' → P y' → P y)
    (hstep : ∀ y, NoBad bad y →
      StepRel (OpRel.eq E) Eq (Skip (fun _ => False) bad Eq) y.observe z.observe → P y) : P y := by
  have hf := Skip.unfold hyz
  clear hyz
  induction hf with
  | step hs => exact hstep _ hy hs
  | silentL h₁ _ ih => exact hsil _ _ h₁ (ih (noBad_silent hy h₁) hstep)
  | extraL _ _ hx => exact hx.elim
  | badL a h₁ hb => exact (hy a hb (.res h₁)).elim

lemma unobserved_succ {m : CoFree E N₁ A} {p : CoFree E N₁ A → Prop}
    (h : ForallUnobserved m p) : ForallUnobserved m fun _ => True :=
  forallUnobserved_mono h fun _ _ => trivial

lemma sameFinite_pure_right {C : CoFree E N₁ A → CoFree E N B → Prop} {x : CoFree E N₁ A}
    {y : CoFree E N B} {b : B} (h : SameFinite Ret C x y) (hy : y.observe = .pure b) :
    ∃ a, Ret a b := by
  induction h with
  | ret a b' _ h₂ hab => rw [hy] at h₂; cases h₂; exact ⟨a, hab⟩
  | impure _ _ h₂ => rw [hy] at h₂; cases h₂
  | silentL _ _ ih => exact ih hy
  | silentR h₂ => rw [hy] at h₂; cases h₂
  | branchL c _ _ ih =>
    obtain ⟨r⟩ := N₁.resp_nonempty c
    exact ih r hy
  | branchR _ h₂ => rw [hy] at h₂; cases h₂
  | mutualUnobservedStep hu =>
    obtain ⟨_, hn, -⟩ := forallUnobserved_exists hu (unobserved_succ hu)
    exact (not_forallUnobserved_pure hy hn).elim

lemma sameFinite_impure_right {x : CoFree E N₁ A} {y : CoFree E N B} {op : E.Op}
    {k : E.Resp op → CoFree E N B} (h : SameFinite Ret (Same Ret) x y)
    (hy : y.observe = .impure op k) (r : E.Resp op) : ∃ x' : CoFree E N₁ A, Same Ret x' (k r) := by
  induction h with
  | ret _ _ _ h₂ => rw [hy] at h₂; cases h₂
  | impure op' _ h₂ hc =>
    rw [hy] at h₂
    cases h₂
    exact ⟨_, hc r⟩
  | silentL _ _ ih => exact ih hy
  | silentR h₂ => rw [hy] at h₂; cases h₂
  | branchL c _ _ ih =>
    obtain ⟨r'⟩ := N₁.resp_nonempty c
    exact ih r' hy
  | branchR _ h₂ => rw [hy] at h₂; cases h₂
  | mutualUnobservedStep hu =>
    obtain ⟨_, hn, -⟩ := forallUnobserved_exists hu (unobserved_succ hu)
    exact (not_forallUnobserved_impure hy hn).elim

lemma Same.hasOutcome_right {x : CoFree E N₁ A} {y : CoFree E N B} {o : Outcome E B}
    (hxy : Same Ret x y) (ho : HasOutcome y o) : ∀ b, o = .res b → ∃ a, Ret a b := by
  induction ho generalizing x with
  | res hv => intro b hb; cases hb; exact sameFinite_pure_right (Same.unfold hxy) hv
  | terminal => intro b hb; cases hb
  | silent _ hm ih => exact ih (Same.silentR_inv hxy hm)
  | branch _ hm ih =>
    obtain ⟨c, k, hm, r, rfl⟩ := hm
    exact ih (Same.branchR_inv hxy hm r)
  | impure _ hm ih =>
    obtain ⟨op, k, hm, r, rfl⟩ := hm
    obtain ⟨x', hx'⟩ := sameFinite_impure_right (Same.unfold hxy) hm r
    exact ih hx'

lemma Same.noBad {x : CoFree E N₁ A} {y : CoFree E N B} (hxy : Same Ret x y)
    (hRet : ∀ a b, Ret a b → ¬bad b) : NoBad bad y := fun b hb ho =>
  let ⟨a, hab⟩ := Same.hasOutcome_right hxy ho b rfl
  hRet a b hab hb

def SkipComp (Ret : A → B → Prop) (bad : B → Prop) {N₁ : NonDeterminism.{u}} :
    CoFree E N₁ A → CoFree E N B → Prop := fun x z =>
  (∃ y, Same Ret x y ∧ NoBad bad y ∧ Skip (fun _ => False) bad Eq y z) ∨ Same Ret x z

lemma same_skip_observable {x : CoFree E N₁ A} {y z : CoFree E N B}
    (hf : SameFinite Ret (Same Ret) x y) (hobs : ¬ForallUnobserved x fun _ => True)
    (hy : NoBad bad y) (hyz : Skip (fun _ => False) bad Eq y z) :
    SameFinite Ret (SkipComp Ret bad) x z := by
  induction hf generalizing z with
  | ret a b hx hy' hab =>
    cases Skip.unfold hyz with
    | step hs =>
      rw [hy'] at hs
      generalize hz : z.observe = sz at hs
      cases sz <;> simp only [StepRel] at hs
      subst hs
      exact .ret a b hx hz hab
    | silentL h₁ => rw [hy'] at h₁; cases h₁
    | extraL _ _ hx => exact hx.elim
    | badL _ h₁ hb => exact (hy _ hb (.res h₁)).elim
  | impure op hx hy' hc =>
    cases Skip.unfold hyz with
    | step hs =>
      rw [hy'] at hs
      generalize hz : z.observe = sz at hs
      cases sz <;> simp only [StepRel, OpRel.eq] at hs
      obtain ⟨rfl, hk⟩ := hs
      exact .impure op hx hz fun r => .inl ⟨_, hc r, noBad_impure hy hy' r, hk r r HEq.rfl⟩
    | silentL h₁ => rw [hy'] at h₁; cases h₁
    | extraL _ _ hx => exact hx.elim
    | badL _ h₁ => rw [hy'] at h₁; cases h₁
  | silentL hx => exact (hobs (by unfold ForallUnobserved; rw [hx]; trivial)).elim
  | branchL c hx => exact (hobs (by unfold ForallUnobserved; rw [hx]; exact fun _ => trivial)).elim
  | silentR hy' _ ih =>
    rename_i y y'
    have hf := Skip.unfold hyz
    cases hf with
    | step hs =>
      rw [hy'] at hs
      generalize hz : z.observe = sz at hs
      cases sz <;> simp only [StepRel] at hs
      exact .silentR hz (ih hobs (noBad_silent hy hy') hs)
    | silentL h₁ hf' =>
      rw [hy'] at h₁
      cases h₁
      exact ih hobs (noBad_silent hy hy') (Skip.fold hf')
    | extraL _ _ hx => exact hx.elim
    | badL _ h₁ => rw [hy'] at h₁; cases h₁
  | branchR c hy' _ ih =>
    have hf := Skip.unfold hyz
    cases hf with
    | step hs =>
      rw [hy'] at hs
      generalize hz : z.observe = sz at hs
      cases sz <;> simp only [StepRel] at hs
      obtain ⟨rfl, hk⟩ := hs
      exact .branchR c hz fun r => ih r hobs (noBad_branch hy hy' r) (hk r r HEq.rfl)
    | silentL h₁ => rw [hy'] at h₁; cases h₁
    | extraL _ _ hx => exact hx.elim
    | badL _ h₁ => rw [hy'] at h₁; cases h₁
  | mutualUnobservedStep hu => exact (hobs (unobserved_succ hu)).elim

lemma sameFinite_visible_right {C C' : CoFree E N₁ A → CoFree E N B → Prop}
    {x : CoFree E N₁ A} {y z : CoFree E N B} (hf : SameFinite Ret C x y)
    (hvis : ¬ForallUnobserved y fun _ => True)
    (hstep : ∀ x, ¬ForallUnobserved x (fun _ => True) → SameFinite Ret C x y →
      SameFinite Ret C' x z) :
    SameFinite Ret C' x z := by
  induction hf with
  | silentL hx _ ih => exact .silentL hx (ih hvis hstep)
  | branchL c hx _ ih => exact .branchL c hx fun r => ih r hvis hstep
  | silentR hy => exact (hvis (by unfold ForallUnobserved; rw [hy]; trivial)).elim
  | branchR c hy => exact (hvis (by unfold ForallUnobserved; rw [hy]; exact fun _ => trivial)).elim
  | mutualUnobservedStep hu =>
    obtain ⟨_, hn, -⟩ := forallUnobserved_exists hu (unobserved_succ hu)
    exact (hvis (unobserved_succ hn)).elim
  | ret a b hx hy hab =>
    refine hstep _ (by unfold ForallUnobserved; rw [hx]; exact id) (.ret a b hx hy hab)
  | impure op hx hy hc =>
    refine hstep _ (by unfold ForallUnobserved; rw [hx]; exact id) (.impure op hx hy hc)

lemma Same.skip {x : CoFree E N₁ A} {y z : CoFree E N B} (hxy : Same Ret x y)
    (hy : NoBad bad y) (hyz : Skip (fun _ => False) bad Eq y z) : Same Ret x z := by
  refine Same.coind (fun x z => ∃ y, Same Ret x y ∧ NoBad bad y ∧
    Skip (fun _ => False) bad Eq y z) (fun x z hxz => ?_) ⟨y, hxy, hy, hyz⟩
  obtain ⟨y, hxy, hy, hyz⟩ := hxz
  by_cases hu : ForallUnobserved x fun _ => True
  · refine skip_peel (P := fun y => Same Ret x y → SameFinite Ret (SkipComp Ret bad) x z) hyz hy
      (fun _ _ h₁ ih h => ih (Same.silentR_inv h h₁)) (fun y hy hs hxy => ?_) hxy
    have hux := Same.unobservedL_inv hxy hu
    generalize hey : y.observe = sy at hs
    generalize hez : z.observe = sz at hs
    cases sy <;> cases sz <;> simp only [StepRel, OpRel.eq] at hs
    · subst hs
      exact sameFinite_visible_right (Same.unfold hxy)
        (by unfold ForallUnobserved; rw [hey]; exact id)
        fun x' hobs hf => same_skip_observable hf hobs hy (Skip.fold (.step (by rw [hey, hez]; rfl)))
    · rename_i y' z'
      refine .mutualUnobservedStep (forallUnobserved_mono hux fun x' hx' => ?_)
      rw [forallUnobserved_silent hez]
      exact .inl ⟨y', Same.silentR_inv hx' hey, noBad_silent hy hey, hs⟩
    · obtain ⟨rfl, hk⟩ := hs
      exact sameFinite_visible_right (Same.unfold hxy)
        (by unfold ForallUnobserved; rw [hey]; exact id)
        fun x' hobs hf => same_skip_observable hf hobs hy
          (Skip.fold (.step (by rw [hey, hez]; exact ⟨rfl, hk⟩)))
    · obtain ⟨rfl, hk⟩ := hs
      refine .mutualUnobservedStep (forallUnobserved_mono hux fun x' hx' => ?_)
      rw [forallUnobserved_branch hez]
      exact fun r => .inl ⟨_, Same.branchR_inv hx' hey r, noBad_branch hy hey r, hk r r HEq.rfl⟩
  · exact same_skip_observable (Same.unfold hxy) hu hy hyz

lemma HasOutcome.skip {y z : CoFree E N B} {o : Outcome E B}
    (hyz : Skip (fun _ => False) bad Eq y z) (hy : NoBad bad y) (ho : HasOutcome z o) :
    HasOutcome y o := by
  induction ho generalizing y with
  | res hv =>
    refine skip_peel (P := fun y => HasOutcome y _) hyz hy (fun _ _ h₁ h => .silent h h₁)
      fun y _ hs => ?_
    rw [hv] at hs
    generalize hey : y.observe = sy at hs
    cases sy <;> simp only [StepRel] at hs
    subst hs
    exact .res hey
  | terminal hr hk =>
    obtain ⟨k, hk⟩ := hk
    refine skip_peel (P := fun y => HasOutcome y _) hyz hy (fun _ _ h₁ h => .silent h h₁)
      fun y _ hs => ?_
    rw [hk] at hs
    generalize hey : y.observe = sy at hs
    cases sy <;> simp only [StepRel, OpRel.eq] at hs
    obtain ⟨rfl, _⟩ := hs
    exact .terminal hr ⟨_, hey⟩
  | silent _ hm ih =>
    refine skip_peel (P := fun y => HasOutcome y _) hyz hy (fun _ _ h₁ h => .silent h h₁)
      fun y hy' hs => ?_
    rw [hm] at hs
    generalize hey : y.observe = sy at hs
    cases sy <;> simp only [StepRel] at hs
    exact .silent (ih hs (noBad_silent hy' hey)) hey
  | branch _ hm ih =>
    obtain ⟨c, k, hm, r, rfl⟩ := hm
    refine skip_peel (P := fun y => HasOutcome y _) hyz hy (fun _ _ h₁ h => .silent h h₁)
      fun y hy' hs => ?_
    rw [hm] at hs
    generalize hey : y.observe = sy at hs
    cases sy <;> simp only [StepRel] at hs
    obtain ⟨rfl, hk⟩ := hs
    exact .branch (ih (hk r r HEq.rfl) (noBad_branch hy' hey r)) ⟨_, _, hey, r, rfl⟩
  | impure _ hm ih =>
    obtain ⟨op, k, hm, r, rfl⟩ := hm
    refine skip_peel (P := fun y => HasOutcome y _) hyz hy (fun _ _ h₁ h => .silent h h₁)
      fun y hy' hs => ?_
    rw [hm] at hs
    generalize hey : y.observe = sy at hs
    cases sy <;> simp only [StepRel, OpRel.eq] at hs
    obtain ⟨rfl, hk⟩ := hs
    exact .impure (ih (hk r r HEq.rfl) (noBad_impure hy' hey r)) ⟨_, _, hey, r, rfl⟩

end Same

end CoFree.Proofs
