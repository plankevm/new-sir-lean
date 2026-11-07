import ITree.Skip.Proofs

universe u

namespace CoFree

variable {E F : Effect.{u}} {N M N₁ : NonDeterminism.{u}} {A B C D : Type u}
  {ex : E.Op → Prop} {bad : A → Prop} {Ret : A → B → Prop}

theorem Skip.congr : ∀ {m₁ m₁' : CoFree E N A} {m₂ m₂' : CoFree E N B},
    m₁.observe = m₁'.observe → m₂.observe = m₂'.observe → Skip ex bad Ret m₁ m₂ →
      Skip ex bad Ret m₁' m₂' :=
  Proofs.Skip.congr

theorem Skip.of_bisim : ∀ {m₁ : CoFree E N A} {m₂ : CoFree E N B},
    Bisim (OpRel.eq E) Ret m₁ m₂ → Skip ex bad Ret m₁ m₂ :=
  Proofs.Skip.of_bisim

theorem Skip.mono : ∀ {ex' : E.Op → Prop} {bad' : A → Prop} {Ret' : A → B → Prop},
    (∀ o, ex o → ex' o) → (∀ a, bad a → bad' a) → (∀ a b, Ret a b → Ret' a b) →
    ∀ {m₁ : CoFree E N A} {m₂ : CoFree E N B}, Skip ex bad Ret m₁ m₂ → Skip ex' bad' Ret' m₁ m₂ :=
  fun hex hbad hRet _ _ h => Proofs.Skip.mono hex hbad hRet h

theorem Skip.pure : ∀ {a : A} {b : B}, Ret a b →
    Skip ex bad Ret (CoFree.pure a : CoFree E N A) (CoFree.pure b) :=
  Proofs.Skip.pure

theorem Skip.extra : ∀ {op : E.Op} {k : E.Resp op → CoFree E N A} {m₁ : CoFree E N A}
    {m₂ : CoFree E N B}, m₁.observe = .impure op k → ex op → (∀ r, Skip ex bad Ret (k r) m₂) →
      Skip ex bad Ret m₁ m₂ :=
  Proofs.Skip.extra

theorem Skip.bind : ∀ {bad' : C → Prop} {Ret' : C → D → Prop} {m₁ : CoFree E N A}
    {m₂ : CoFree E N B} {g₁ : A → CoFree E N C} {g₂ : B → CoFree E N D},
    Skip ex bad Ret m₁ m₂ → (∀ a b, Ret a b → Skip ex bad' Ret' (g₁ a) (g₂ b)) →
    (∀ a, bad a → ∃ c, (g₁ a).observe = .pure c ∧ bad' c) →
      Skip ex bad' Ret' (m₁.bind g₁) (m₂.bind g₂) :=
  Proofs.Skip.bind

theorem Skip.prefix : ∀ {P : A → Prop} {bad' : C → Prop} {Ret' : C → D → Prop}
    {m : CoFree E N A} {g : A → CoFree E N C} {n : CoFree E N D},
    Skip ex (fun _ => False) (fun a (_ : PUnit) => P a) m (CoFree.pure ⟨⟩) →
    (∀ a, P a → Skip ex bad' Ret' (g a) n) → Skip ex bad' Ret' (m.bind g) n :=
  Proofs.Skip.prefix

theorem Skip.mapOps : ∀ {ex' : F.Op → Prop} (e : Effect.Map E F) (nd : NonDeterminism.Map N M),
    (∀ o, ex o → ex' (e.op o)) → ∀ {m₁ : CoFree E N A} {m₂ : CoFree E N B},
    Skip ex bad Ret m₁ m₂ → Skip ex' bad Ret (m₁.mapOps e nd) (m₂.mapOps e nd) :=
  fun e nd hex _ _ h => Proofs.Skip.mapOps e nd hex h

theorem Skip.loop : ∀ {β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) {Ret : β₁ → β₂ → Prop}
    {f₁ : Unit → β₁ → CoFree E N (ForInStep β₁)} {f₂ : Unit → β₂ → CoFree E N (ForInStep β₂)},
    (∀ b₁ b₂, RB b₁ b₂ → Skip ex (fun _ => False) (LoopRel RB Ret) (f₁ () b₁) (f₂ () b₂)) →
    ∀ {b₁ b₂}, RB b₁ b₂ →
      Skip ex (fun _ => False) Ret (forIn Lean.Loop.mk b₁ f₁) (forIn Lean.Loop.mk b₂ f₂) :=
  fun RB _ _ _ hf _ _ h => Proofs.Skip.loop RB hf h

theorem Skip.forIn_array_filter : ∀ {α β₁ β₂ : Type u} (RB : β₁ → β₂ → Prop) (keep : α → Bool)
    {f₁ : α → β₁ → CoFree E N (ForInStep β₁)} {f₂ : α → β₂ → CoFree E N (ForInStep β₂)}
    (xs : Array α),
    (∀ a ∈ xs, keep a → ∀ b₁ b₂, RB b₁ b₂ →
      Skip ex (fun _ => False) (ForInRel RB) (f₁ a b₁) (f₂ a b₂)) →
    (∀ a ∈ xs, keep a = false → ∀ b₁ b₂, RB b₁ b₂ →
      Skip ex (fun _ => False) (ForInRel RB) (f₁ a b₁) (CoFree.pure (.yield b₂))) →
    ∀ {b₁ b₂}, RB b₁ b₂ →
      Skip ex (fun _ => False) RB (forIn xs b₁ f₁) (forIn (xs.filter keep) b₂ f₂) :=
  fun RB keep _ _ xs hk hd _ _ h => Proofs.Skip.forIn_array_filter RB keep xs hk hd h

theorem Skip.fix : ∀ {I O : Type u}
    {f₁ f₂ : (I → CoFree (Effect.Rec I O E) N O) → I → CoFree (Effect.Rec I O E) N O},
    (∀ i, Skip (recExtra ex) (fun _ => False) Eq
      (f₁ (fun j => perform (E := Effect.Rec I O E) (.inl j)) i)
      (f₂ (fun j => perform (E := Effect.Rec I O E) (.inl j)) i)) →
    ∀ i, Skip ex (fun _ => False) Eq (CoFree.fix f₁ i) (CoFree.fix f₂ i) :=
  fun hbody i => Proofs.Skip.fix hbody i

theorem Skip.interp : ∀ {σ : Type u} (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X)),
    (∀ {X Y : Type u} (st : σ) (s : Step E N A X) (f : X → Y),
      h st (s.map f) = (h st s).map fun q => (q.1, f q.2)) →
    ∀ {ex' : F.Op → Prop} {bad' : B → Prop},
    (∀ {X : Type u} (st : σ) (x : X), h st (.silent x) = .silent (st, x)) →
    (∀ (st : σ) (op : E.Op), ex op → HandledExtra ex' bad' st (h st (.impure op fun r => r))) →
    (∀ {X : Type u} (st : σ) (a : A), bad a → ∃ b, h (X := X) st (.pure a) = .pure b ∧ bad' b) →
    ∀ {m₁ m₂ : CoFree E N A}, Skip ex bad Eq m₁ m₂ →
      ∀ (st : σ), Skip ex' bad' Eq (CoFree.interp h st m₁) (CoFree.interp h st m₂) :=
  fun h hnat _ _ hsilent hextra hbad _ _ hm st =>
    Proofs.Skip.interp h hnat hsilent hextra hbad hm st

theorem Same.noBad : ∀ {Ret : A → B → Prop} {bad : B → Prop} {x : CoFree E N₁ A}
    {y : CoFree E N B}, Same Ret x y → (∀ a b, Ret a b → ¬bad b) → NoBad bad y :=
  Proofs.Same.noBad

theorem Same.hasOutcome_right : ∀ {Ret : A → B → Prop} {x : CoFree E N₁ A} {y : CoFree E N B}
    {b : B}, Same Ret x y → HasOutcome y (.res b) → ∃ a, Ret a b :=
  fun hxy ho => Proofs.Same.hasOutcome_right hxy ho _ rfl

theorem Same.skip : ∀ {Ret : A → B → Prop} {bad : B → Prop} {x : CoFree E N₁ A}
    {y z : CoFree E N B}, Same Ret x y → NoBad bad y → Skip (fun _ => False) bad Eq y z →
      Same Ret x z :=
  Proofs.Same.skip

theorem HasOutcome.skip : ∀ {bad : B → Prop} {y z : CoFree E N B} {o : Outcome E B},
    Skip (fun _ => False) bad Eq y z → NoBad bad y → HasOutcome z o → HasOutcome y o :=
  Proofs.HasOutcome.skip

end CoFree
