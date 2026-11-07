import ITree.Refute
import ITree.Same.Theorems
import ITree.Outcome

universe u

namespace CoFree.Proofs

variable {E : Effect.{u}} {N N₁ N₂ : NonDeterminism.{u}} {A B : Type u} {Ret : A → B → Prop}

section Steps

lemma ustep_forall {m m' : CoFree E N A} {p : CoFree E N A → Prop} (h : UStep m m')
    (hp : ForallUnobserved m p) : p m' := by
  rcases h with h | ⟨c, k, r, h, rfl⟩
  · exact (forallUnobserved_silent h).1 hp
  · exact (forallUnobserved_branch h).1 hp r

lemma ustep_unobserved {m m' : CoFree E N A} (h : UStep m m') : ForallUnobserved m fun _ => True := by
  rcases h with h | ⟨c, k, r, h, rfl⟩
  · exact (forallUnobserved_silent h).2 trivial
  · exact (forallUnobserved_branch h).2 fun _ => trivial

lemma forall_of_ustep {m : CoFree E N A} {p : CoFree E N A → Prop}
    (hu : ForallUnobserved m fun _ => True) (h : ∀ m', UStep m m' → p m') : ForallUnobserved m p := by
  unfold ForallUnobserved at hu ⊢
  split at hu
  · rename_i m' hm; exact h m' (.inl hm)
  · rename_i c k hm; exact fun r => h _ (.inr ⟨c, k, r, hm, rfl⟩)
  · exact hu.elim

lemma visible_cases {m : CoFree E N A} (h : Visible m) :
    (∃ a, m.observe = .pure a) ∨ ∃ op k, m.observe = .impure op k := by
  unfold Visible ForallUnobserved at h
  split at h
  · exact (h trivial).elim
  · exact (h fun _ => trivial).elim
  · rename_i hn₁ hn₂
    generalize hm : m.observe = s at hn₁ hn₂
    rcases s with a | m' | ⟨op, k⟩ | ⟨c, k⟩
    · exact .inl ⟨a, rfl⟩
    · exact (hn₁ m' rfl).elim
    · exact .inr ⟨op, k, rfl⟩
    · exact (hn₂ c k rfl).elim

lemma visible_pure {m : CoFree E N A} {a : A} (h : m.observe = .pure a) : Visible m :=
  not_forallUnobserved_pure h

lemma visible_impure {m : CoFree E N A} {op : E.Op} {k : E.Resp op → CoFree E N A}
    (h : m.observe = .impure op k) : Visible m :=
  not_forallUnobserved_impure h

lemma Same.ustepL {x x' : CoFree E N₁ A} {y : CoFree E N₂ B} (h : Same Ret x y) (hs : UStep x x') :
    Same Ret x' y :=
  ustep_forall (p := fun n => Same Ret n y) hs (Same.unobservedL_inv h (ustep_unobserved hs))

lemma Same.ustepR {x : CoFree E N₁ A} {y y' : CoFree E N₂ B} (h : Same Ret x y) (hs : UStep y y') :
    Same Ret x y' :=
  ustep_forall hs (Same.unobservedR_inv h (ustep_unobserved hs))

end Steps

section NotBad

lemma same_visMatch {x : CoFree E N₁ A} {y : CoFree E N₂ B} (h : Same Ret x y) (hx : Visible x)
    (hy : Visible y) : VisMatch x y := by
  rcases visible_cases hx with ⟨a, ha⟩ | ⟨op, k, ha⟩ <;>
    rcases visible_cases hy with ⟨b, hb⟩ | ⟨op', k', hb⟩
  · exact .inl ⟨a, b, ha, hb⟩
  · have hf := Same.unfold h
    cases hf with
    | ret _ _ _ h₂ => rw [hb] at h₂; cases h₂
    | impure _ h₁ => rw [ha] at h₁; cases h₁
    | silentL h₁ => rw [ha] at h₁; cases h₁
    | silentR h₂ => rw [hb] at h₂; cases h₂
    | branchL _ h₁ => rw [ha] at h₁; cases h₁
    | branchR _ h₂ => rw [hb] at h₂; cases h₂
    | mutualUnobservedStep hu => exact (not_forallUnobserved_pure ha hu).elim
  · have hf := Same.unfold h
    cases hf with
    | ret _ _ h₁ => rw [ha] at h₁; cases h₁
    | impure _ _ h₂ => rw [hb] at h₂; cases h₂
    | silentL h₁ => rw [ha] at h₁; cases h₁
    | silentR h₂ => rw [hb] at h₂; cases h₂
    | branchL _ h₁ => rw [ha] at h₁; cases h₁
    | branchR _ h₂ => rw [hb] at h₂; cases h₂
    | mutualUnobservedStep hu => exact (not_forallUnobserved_impure ha hu).elim
  · cases Same.impure_inv h ha hb
    exact .inr ⟨op, k, k', ha, hb⟩

lemma sameFinite_div_left {C : CoFree E N₁ A → CoFree E N₂ B → Prop} {f : Nat → CoFree E N₁ A}
    (hc : Chain f) {x : CoFree E N₁ A} {y : CoFree E N₂ B} (h : SameFinite Ret C x y) :
    Visible y → ∀ n, f n = x → False := by
  induction h with
  | ret _ _ h₁ =>
    intro _ n hn; subst hn
    rcases hc n with h | ⟨_, _, _, h, _⟩ <;> rw [h₁] at h <;> cases h
  | impure _ h₁ =>
    intro _ n hn; subst hn
    rcases hc n with h | ⟨_, _, _, h, _⟩ <;> rw [h₁] at h <;> cases h
  | silentL h₁ _ ih =>
    intro hv n hn; subst hn
    rcases hc n with h | ⟨_, _, _, h, _⟩ <;> rw [h₁] at h <;> cases h
    exact ih hv (n + 1) rfl
  | silentR h₂ => intro hv; exact (hv ((forallUnobserved_silent h₂).2 trivial)).elim
  | branchL c h₁ _ ih =>
    intro hv n hn; subst hn
    rcases hc n with h | ⟨_, _, r, h, hk⟩ <;> rw [h₁] at h <;> cases h
    exact ih r hv (n + 1) hk.symm
  | branchR c h₂ => intro hv; exact (hv ((forallUnobserved_branch h₂).2 fun _ => trivial)).elim
  | mutualUnobservedStep hu =>
    intro hv
    obtain ⟨_, hn, -⟩ := forallUnobserved_exists hu hu
    exact (hv (forallUnobserved_mono hn fun _ _ => trivial)).elim

lemma sameFinite_div_right {C : CoFree E N₁ A → CoFree E N₂ B → Prop} {f : Nat → CoFree E N₂ B}
    (hc : Chain f) {x : CoFree E N₁ A} {y : CoFree E N₂ B} (h : SameFinite Ret C x y) :
    Visible x → ∀ n, f n = y → False := by
  induction h with
  | ret _ _ _ h₂ =>
    intro _ n hn; subst hn
    rcases hc n with h | ⟨_, _, _, h, _⟩ <;> rw [h₂] at h <;> cases h
  | impure _ _ h₂ =>
    intro _ n hn; subst hn
    rcases hc n with h | ⟨_, _, _, h, _⟩ <;> rw [h₂] at h <;> cases h
  | silentR h₂ _ ih =>
    intro hv n hn; subst hn
    rcases hc n with h | ⟨_, _, _, h, _⟩ <;> rw [h₂] at h <;> cases h
    exact ih hv (n + 1) rfl
  | silentL h₁ => intro hv; exact (hv ((forallUnobserved_silent h₁).2 trivial)).elim
  | branchR c h₂ _ ih =>
    intro hv n hn; subst hn
    rcases hc n with h | ⟨_, _, r, h, hk⟩ <;> rw [h₂] at h <;> cases h
    exact ih r hv (n + 1) hk.symm
  | branchL c h₁ => intro hv; exact (hv ((forallUnobserved_branch h₁).2 fun _ => trivial)).elim
  | mutualUnobservedStep hu =>
    intro hv
    exact (hv (forallUnobserved_mono hu fun _ _ => trivial)).elim

lemma Same.not_bad {x : CoFree E N₁ A} {y : CoFree E N₂ B} (h : Bad Ret x y) : ¬Same Ret x y := by
  induction h with
  | ret a b h₁ h₂ hn => exact fun hs => hn (Same.ret_inv hs h₁ h₂)
  | mismatch hx hy hn => exact fun hs => hn (same_visMatch hs hx hy)
  | impure op r h₁ h₂ _ ih => exact fun hs => ih (Same.impure_inv_resp hs h₁ h₂ r)
  | both h₁ h₂ _ ih => exact fun hs => ih (Same.ustepR (Same.ustepL hs h₁) h₂)
  | left h₁ _ _ ih => exact fun hs => ih (Same.ustepL hs h₁)
  | right _ h₂ _ ih => exact fun hs => ih (Same.ustepR hs h₂)
  | divL f hc h0 hv => exact fun hs => sameFinite_div_left hc (Same.unfold hs) hv 0 h0
  | divR f hv hc h0 => exact fun hs => sameFinite_div_right hc (Same.unfold hs) hv 0 h0

end NotBad

section OfNotBad

lemma exists_chain_of_not_acc {x : CoFree E N A} (h : ¬Acc (fun a b => UStep b a) x) :
    ∃ f, Chain f ∧ f 0 = x := by
  have step : ∀ m : CoFree E N A, ¬Acc (fun a b => UStep b a) m →
      ∃ m', UStep m m' ∧ ¬Acc (fun a b => UStep b a) m' := by
    intro m hm
    refine Classical.byContradiction fun hn => hm (.intro _ fun m' hm' => ?_)
    exact Classical.byContradiction fun hacc => hn ⟨m', hm', hacc⟩
  let g : {m // ¬Acc (fun a b => UStep b a) m} → {m // ¬Acc (fun a b => UStep b a) m} :=
    fun m => ⟨Classical.choose (step m.1 m.2), (Classical.choose_spec (step m.1 m.2)).2⟩
  let s : Nat → {m // ¬Acc (fun a b => UStep b a) m} := fun n =>
    Nat.rec (motive := fun _ => {m // ¬Acc (fun a b => UStep b a) m}) ⟨x, h⟩ (fun _ m => g m) n
  exact ⟨fun n => (s n).1, fun n => (Classical.choose_spec (step (s n).1 (s n).2)).1, rfl⟩

lemma both_visible {x : CoFree E N₁ A} {y : CoFree E N₂ B} (h : ¬Bad Ret x y) (hx : Visible x)
    (hy : Visible y) : SameFinite Ret (fun x y => ¬Bad Ret x y ∨ Same Ret x y) x y := by
  by_cases hm : VisMatch x y
  · rcases hm with ⟨a, b, ha, hb⟩ | ⟨op, k₁, k₂, ha, hb⟩
    · exact .ret a b ha hb (Classical.byContradiction fun hn => h (.ret a b ha hb hn))
    · exact .impure op ha hb fun r => .inl fun hb' => h (.impure op r ha hb hb')
  · exact (h (.mismatch hx hy hm)).elim

lemma Same.of_not_bad {x : CoFree E N₁ A} {y : CoFree E N₂ B} (h : ¬Bad Ret x y) : Same Ret x y := by
  refine Same.coind (fun x y => ¬Bad Ret x y) (fun x y h => ?_) h
  by_cases hx : Visible x <;> by_cases hy : Visible y
  · exact both_visible h hx hy
  · have hy' : ForallUnobserved y fun _ => True := Classical.byContradiction hy
    have hacc : Acc (fun a b => UStep b a) y := Classical.byContradiction fun hn => by
      obtain ⟨f, hc, h0⟩ := exists_chain_of_not_acc hn
      exact h (.divR f hx hc h0)
    clear hy hy'
    induction hacc with
    | intro y _ ih =>
      by_cases hy : Visible y
      · exact both_visible h hx hy
      · have hy' : ForallUnobserved y fun _ => True := Classical.byContradiction hy
        unfold ForallUnobserved at hy'
        split at hy'
        · rename_i y' hm
          exact .silentR hm (ih y' (.inl hm) fun hb => h (.right hx (.inl hm) hb))
        · rename_i c k hm
          exact .branchR c hm fun r =>
            ih (k r) (.inr ⟨c, k, r, hm, rfl⟩) fun hb => h (.right hx (.inr ⟨c, k, r, hm, rfl⟩) hb)
        · exact hy'.elim
  · have hx' : ForallUnobserved x fun _ => True := Classical.byContradiction hx
    have hacc : Acc (fun a b => UStep b a) x := Classical.byContradiction fun hn => by
      obtain ⟨f, hc, h0⟩ := exists_chain_of_not_acc hn
      exact h (.divL f hc h0 hy)
    clear hx hx'
    induction hacc with
    | intro x _ ih =>
      by_cases hx : Visible x
      · exact both_visible h hx hy
      · have hx' : ForallUnobserved x fun _ => True := Classical.byContradiction hx
        unfold ForallUnobserved at hx'
        split at hx'
        · rename_i x' hm
          exact .silentL hm (ih x' (.inl hm) fun hb => h (.left (.inl hm) hy hb))
        · rename_i c k hm
          exact .branchL c hm fun r =>
            ih (k r) (.inr ⟨c, k, r, hm, rfl⟩) fun hb => h (.left (.inr ⟨c, k, r, hm, rfl⟩) hy hb)
        · exact hx'.elim
  · have hx' : ForallUnobserved x fun _ => True := Classical.byContradiction hx
    have hy' : ForallUnobserved y fun _ => True := Classical.byContradiction hy
    exact .mutualUnobservedStep (forall_of_ustep hx' fun x' hx'' =>
      forall_of_ustep hy' fun y' hy'' => .inl fun hb => h (.both hx'' hy'' hb))

end OfNotBad

section Outcome

lemma sameFinite_hasOutcome_pure {x : CoFree E N₁ A} {y : CoFree E N₂ B} {b : B}
    {C : CoFree E N₁ A → CoFree E N₂ B → Prop} (h : SameFinite Ret C x y) (hy : y.observe = .pure b) :
    ∃ a, HasOutcome x (.res a) ∧ Ret a b := by
  induction h with
  | ret a b' hx h₂ hab => rw [hy] at h₂; cases h₂; exact ⟨a, .res hx, hab⟩
  | impure _ _ h₂ => rw [hy] at h₂; cases h₂
  | silentL hx _ ih => obtain ⟨a, ha, hab⟩ := ih hy; exact ⟨a, .silent ha hx, hab⟩
  | silentR h₂ => rw [hy] at h₂; cases h₂
  | branchL c hx _ ih =>
    obtain ⟨r⟩ := N₁.resp_nonempty c
    obtain ⟨a, ha, hab⟩ := ih r hy
    exact ⟨a, .branch ha ⟨c, _, hx, r, rfl⟩, hab⟩
  | branchR _ h₂ => rw [hy] at h₂; cases h₂
  | mutualUnobservedStep hu =>
    obtain ⟨_, hn, -⟩ := forallUnobserved_exists hu hu
    exact (not_forallUnobserved_pure hy hn).elim

lemma sameFinite_hasOutcome_impure {x : CoFree E N₁ A} {y : CoFree E N₂ B} {b : B} {op : E.Op}
    {k : E.Resp op → CoFree E N₂ B} {r : E.Resp op} (h : SameFinite Ret (Same Ret) x y)
    (hy : y.observe = .impure op k)
    (ih : ∀ x' : CoFree E N₁ A, Same Ret x' (k r) → ∃ a, HasOutcome x' (.res a) ∧ Ret a b) :
    ∃ a, HasOutcome x (.res a) ∧ Ret a b := by
  induction h with
  | ret _ _ _ h₂ => rw [hy] at h₂; cases h₂
  | impure op' hx h₂ hc =>
    rw [hy] at h₂
    cases h₂
    obtain ⟨a, ha, hab⟩ := ih _ (hc r)
    exact ⟨a, .impure ha ⟨_, _, hx, r, rfl⟩, hab⟩
  | silentL hx _ ih' => obtain ⟨a, ha, hab⟩ := ih' hy; exact ⟨a, .silent ha hx, hab⟩
  | silentR h₂ => rw [hy] at h₂; cases h₂
  | branchL c hx _ ih' =>
    obtain ⟨r'⟩ := N₁.resp_nonempty c
    obtain ⟨a, ha, hab⟩ := ih' r' hy
    exact ⟨a, .branch ha ⟨c, _, hx, r', rfl⟩, hab⟩
  | branchR _ h₂ => rw [hy] at h₂; cases h₂
  | mutualUnobservedStep hu =>
    obtain ⟨_, hn, -⟩ := forallUnobserved_exists hu hu
    exact (not_forallUnobserved_impure hy hn).elim

lemma Same.hasOutcome_left {x : CoFree E N₁ A} {y : CoFree E N₂ B} {o : Outcome E B}
    (h : Same Ret x y) (ho : HasOutcome y o) : ∀ b, o = .res b → ∃ a, HasOutcome x (.res a) ∧ Ret a b := by
  induction ho generalizing x with
  | res hv => intro b hb; cases hb; exact sameFinite_hasOutcome_pure (Same.unfold h) hv
  | terminal => intro b hb; cases hb
  | silent _ hm ih => exact ih (Same.silentR_inv h hm)
  | branch _ hm ih =>
    obtain ⟨c, k, hm, r, rfl⟩ := hm
    exact ih (Same.branchR_inv h hm r)
  | impure _ hm ih =>
    obtain ⟨op, k, hm, r, rfl⟩ := hm
    intro b hb
    exact sameFinite_hasOutcome_impure (Same.unfold h) hm fun x' hx' => ih hx' b hb

end Outcome

end CoFree.Proofs
