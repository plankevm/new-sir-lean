import ITree.Bisim.Proofs

universe u

namespace CoFree

variable {E F : Effect.{u}} {N M N₁ : NonDeterminism.{u}} {A B C D : Type u}
  {ρ : OpRel E} {Ret : A → B → Prop}

theorem Bisim.unfold : ∀ {m₁ : CoFree E N A} {m₂ : CoFree E N B},
    Bisim ρ Ret m₁ m₂ → StepRel ρ Ret (Bisim ρ Ret) m₁.observe m₂.observe :=
  Proofs.Bisim.unfold

theorem Bisim.fold : ∀ {m₁ : CoFree E N A} {m₂ : CoFree E N B},
    StepRel ρ Ret (Bisim ρ Ret) m₁.observe m₂.observe → Bisim ρ Ret m₁ m₂ :=
  Proofs.Bisim.fold

theorem Bisim.coind : ∀ (R : CoFree E N A → CoFree E N B → Prop),
    (∀ x y, R x y → StepRel ρ Ret (fun a b => R a b ∨ Bisim ρ Ret a b) x.observe y.observe) →
    ∀ {m₁ m₂}, R m₁ m₂ → Bisim ρ Ret m₁ m₂ :=
  fun R hR _ _ h => Proofs.Bisim.coind R hR h

theorem Bisim.congr : ∀ {m₁ m₁' : CoFree E N A} {m₂ m₂' : CoFree E N B},
    m₁.observe = m₁'.observe → m₂.observe = m₂'.observe → Bisim ρ Ret m₁ m₂ →
      Bisim ρ Ret m₁' m₂' :=
  Proofs.Bisim.congr

theorem Bisim.mono : ∀ {Ret' : A → B → Prop}, (∀ a b, Ret a b → Ret' a b) →
    ∀ {m₁ : CoFree E N A} {m₂ : CoFree E N B}, Bisim ρ Ret m₁ m₂ → Bisim ρ Ret' m₁ m₂ :=
  fun hRet _ _ h => Proofs.Bisim.mono hRet h

theorem Bisim.pure : ∀ {a : A} {b : B}, Ret a b →
    Bisim ρ Ret (CoFree.pure a : CoFree E N A) (CoFree.pure b) :=
  Proofs.Bisim.pure

theorem Bisim.refl : ∀ {Ret : A → A → Prop}, (∀ a, Ret a a) →
    ∀ (m : CoFree E N A), Bisim (OpRel.eq E) Ret m m :=
  Proofs.Bisim.refl

theorem Bisim.symm : ∀ {m₁ m₂ : CoFree E N A},
    Bisim (OpRel.eq E) Eq m₁ m₂ → Bisim (OpRel.eq E) Eq m₂ m₁ :=
  Proofs.Bisim.symm

theorem Bisim.bind : ∀ {Ret' : C → D → Prop} {m₁ : CoFree E N A} {m₂ : CoFree E N B}
    {g₁ : A → CoFree E N C} {g₂ : B → CoFree E N D},
    Bisim ρ Ret m₁ m₂ → (∀ a b, Ret a b → Bisim ρ Ret' (g₁ a) (g₂ b)) →
      Bisim ρ Ret' (m₁.bind g₁) (m₂.bind g₂) :=
  Proofs.Bisim.bind

theorem Bisim.mapOps : ∀ {ρ' : OpRel F} {e : Effect.Map E F} {nd : NonDeterminism.Map N M}
    {m₁ : CoFree E N A} {m₂ : CoFree E N B},
    (∀ o₁ o₂, ρ.op o₁ o₂ → ρ'.op (e.op o₁) (e.op o₂)) →
    (∀ o₁ o₂ r₁ r₂, ρ.op o₁ o₂ → ρ'.resp (e.op o₁) (e.op o₂) r₁ r₂ →
      ρ.resp o₁ o₂ (e.resp o₁ r₁) (e.resp o₂ r₂)) →
    Bisim ρ Ret m₁ m₂ → Bisim ρ' Ret (m₁.mapOps e nd) (m₂.mapOps e nd) :=
  Proofs.Bisim.mapOps

theorem Bisim.iter : ∀ {S₁ S₂ : Type u} (RS : S₁ → S₂ → Prop)
    {g₁ : S₁ → CoFree E N (IterStep S₁ A)} {g₂ : S₂ → CoFree E N (IterStep S₂ B)},
    (∀ s₁ s₂, RS s₁ s₂ → Bisim ρ (IterRel RS Ret) (g₁ s₁) (g₂ s₂)) →
    ∀ {s₁ s₂}, RS s₁ s₂ → Bisim ρ Ret (iter s₁ g₁) (iter s₂ g₂) :=
  fun RS _ _ hg _ _ h => Proofs.Bisim.iter RS hg h

theorem Bisim.loop : ∀ {β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) {Ret : β₁ → β₂ → Prop}
    {f₁ : Unit → β₁ → CoFree E N (ForInStep β₁)} {f₂ : Unit → β₂ → CoFree E N (ForInStep β₂)},
    (∀ b₁ b₂, RB b₁ b₂ → Bisim ρ (LoopRel RB Ret) (f₁ () b₁) (f₂ () b₂)) →
    ∀ {b₁ b₂}, RB b₁ b₂ → Bisim ρ Ret (forIn Lean.Loop.mk b₁ f₁) (forIn Lean.Loop.mk b₂ f₂) :=
  fun RB _ _ _ hf _ _ h => Proofs.Bisim.loop RB hf h

theorem Bisim.forIn_array : ∀ {α₁ α₂ β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) (φ : α₁ → α₂)
    {f₁ : α₁ → β₁ → CoFree E N (ForInStep β₁)} {f₂ : α₂ → β₂ → CoFree E N (ForInStep β₂)}
    (xs : Array α₁),
    (∀ a ∈ xs, ∀ b₁ b₂, RB b₁ b₂ → Bisim ρ (ForInRel RB) (f₁ a b₁) (f₂ (φ a) b₂)) →
    ∀ {b₁ b₂}, RB b₁ b₂ → Bisim ρ RB (forIn xs b₁ f₁) (forIn (xs.map φ) b₂ f₂) :=
  fun RB φ _ _ xs hf _ _ h => Proofs.Bisim.forIn_array RB φ xs hf h

theorem Bisim.forIn_array_filter : ∀ {α β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) (keep : α → Bool)
    {f₁ : α → β₁ → CoFree E N (ForInStep β₁)} {f₂ : α → β₂ → CoFree E N (ForInStep β₂)}
    (xs : Array α),
    (∀ a ∈ xs, keep a → ∀ b₁ b₂, RB b₁ b₂ → Bisim ρ (ForInRel RB) (f₁ a b₁) (f₂ a b₂)) →
    (∀ a ∈ xs, keep a = false → ∀ b, (f₁ a b).observe = .pure (.yield b)) →
    ∀ {b₁ b₂}, RB b₁ b₂ → Bisim ρ RB (forIn xs b₁ f₁) (forIn (xs.filter keep) b₂ f₂) :=
  fun RB keep _ _ xs hk hd _ _ h => Proofs.Bisim.forIn_array_filter RB keep xs hk hd h

theorem Bisim.fix : ∀ {I O : Type u} {RI : I → I → Prop}
    {f₁ f₂ : (I → CoFree (Effect.Rec I O E) N O) → I → CoFree (Effect.Rec I O E) N O},
    (∀ i₁ i₂, RI i₁ i₂ → Bisim (OpRel.calls RI ρ) Eq
      (f₁ (fun j => perform (E := Effect.Rec I O E) (.inl j)) i₁)
      (f₂ (fun j => perform (E := Effect.Rec I O E) (.inl j)) i₂)) →
    ∀ {i₁ i₂}, RI i₁ i₂ → Bisim ρ Eq (CoFree.fix f₁ i₁) (CoFree.fix f₂ i₂) :=
  fun hbody _ _ hi => Proofs.Bisim.fix hbody hi

theorem Bisim.call : ∀ {I O : Type u} {RI : I → I → Prop} {Ret : O → O → Prop}, (∀ o, Ret o o) →
    ∀ {i₁ i₂}, RI i₁ i₂ →
      Bisim (OpRel.calls RI ρ) Ret (perform (E := Effect.Rec I O E) (N := N) (.inl i₁))
        (perform (E := Effect.Rec I O E) (.inl i₂)) :=
  Proofs.Bisim.call

theorem Bisim.interp : ∀ {σ : Type u} (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X)),
    (∀ {X Y : Type u} (st : σ) (s : Step E N A X) (f : X → Y),
      h st (s.map f) = (h st s).map fun q => (q.1, f q.2)) →
    ∀ {m₁ m₂ : CoFree E N A}, Bisim (OpRel.eq E) Eq m₁ m₂ →
      ∀ (st : σ), Bisim (OpRel.eq F) Eq (CoFree.interp h st m₁) (CoFree.interp h st m₂) :=
  fun h hnat _ _ hm st => Proofs.Bisim.interp h hnat hm st

theorem Same.bisim : ∀ {x : CoFree E N₁ A} {y z : CoFree E N B},
    Same Ret x y → Bisim (OpRel.eq E) Eq y z → Same Ret x z :=
  Proofs.Same.bisim

theorem Bisim.same : ∀ {x y : CoFree E N A} {z : CoFree E N₁ B},
    Bisim (OpRel.eq E) Eq x y → Same Ret y z → Same Ret x z :=
  Proofs.Bisim.same

theorem Deterministic.bisim : ∀ {x y : CoFree E N A},
    Deterministic x → Bisim (OpRel.eq E) Eq x y → Deterministic y :=
  Proofs.Deterministic.bisim

theorem HasOutcome.bisim : ∀ {m₁ m₂ : CoFree E N A} {o : Outcome E A},
    HasOutcome m₁ o → Bisim (OpRel.eq E) Eq m₁ m₂ → HasOutcome m₂ o :=
  Proofs.HasOutcome.bisim

end CoFree
