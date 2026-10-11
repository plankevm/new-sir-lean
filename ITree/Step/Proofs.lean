import ITree.Step

universe u w₁ w₂ w₃ w₄

namespace Step.Proofs

variable {E : Effect.{u}} {A : Type u}

theorem map_pure {S : Type w₁} {T : Type w₂} (f : S → T) (a : A) :
    (Step.pure a : Step E A S).map f = .pure a := rfl

theorem map_silent {S : Type w₁} {T : Type w₂} (f : S → T) (s : S) :
    (Step.silent s : Step E A S).map f = .silent (f s) := rfl

theorem map_impure {S : Type w₁} {T : Type w₂} (f : S → T) (op : E.Op)
    (k : E.Resp op → S) : (Step.impure op k : Step E A S).map f = .impure op fun r => f (k r) :=
  rfl

theorem map_map {S : Type w₁} {T : Type w₂} {U : Type w₃} (f : S → T) (g : T → U)
    (x : Step E A S) : (x.map f).map g = x.map fun s => g (f s) := by
  cases x <;> rfl

theorem map_congr {S : Type w₁} {T : Type w₂} {f g : S → T} (h : ∀ s, f s = g s)
    (x : Step E A S) : x.map f = x.map g := by
  cases x <;> simp only [map, h]

theorem Rel.refl {S : Type w₁} {R : S → S → Prop} (hR : ∀ s, R s s) :
    ∀ x : Step E A S, Rel R x x
  | .pure a => .pure a
  | .silent s => .silent (hR s)
  | .impure op k => .impure op fun r => hR (k r)

theorem Rel.symm {S : Type w₁} {T : Type w₂} {R : S → T → Prop}
    {x : Step E A S} {y : Step E A T} (h : Rel R x y) : Rel (fun t s => R s t) y x := by
  cases h with
  | pure a => exact .pure a
  | silent h => exact .silent h
  | impure op h => exact .impure op h

theorem Rel.trans {S : Type w₁} {T : Type w₂} {U : Type w₃}
    {R₁ : S → T → Prop} {R₂ : T → U → Prop}
    {x : Step E A S} {y : Step E A T} {z : Step E A U}
    (h₁ : Rel R₁ x y) (h₂ : Rel R₂ y z) :
    Rel (fun s u => ∃ t, R₁ s t ∧ R₂ t u) x z := by
  cases h₁ with
  | pure a => cases h₂; exact .pure a
  | silent h₁ => cases h₂ with
    | silent h₂ => exact .silent ⟨_, h₁, h₂⟩
  | impure op h₁ => cases h₂ with
    | impure _ h₂ => exact .impure op fun r => ⟨_, h₁ r, h₂ r⟩

theorem Rel.mono {S : Type w₁} {T : Type w₂} {R R' : S → T → Prop}
    {x : Step E A S} {y : Step E A T}
    (h : Rel R x y) (hR : ∀ s t, R s t → R' s t) : Rel R' x y := by
  cases h with
  | pure a => exact .pure a
  | silent h => exact .silent (hR _ _ h)
  | impure op h => exact .impure op fun r => hR _ _ (h r)

theorem Rel.map {S : Type w₁} {T : Type w₂} {S' : Type w₃} {T' : Type w₄}
    {R : S → T → Prop} {R' : S' → T' → Prop} {f : S → S'} {g : T → T'}
    {x : Step E A S} {y : Step E A T}
    (h : Rel R x y) (hfg : ∀ s t, R s t → R' (f s) (g t)) :
    Rel R' (x.map f) (y.map g) := by
  cases h with
  | pure a => exact .pure a
  | silent h => exact .silent (hfg _ _ h)
  | impure op h => exact .impure op fun r => hfg _ _ (h r)

theorem Rel.of_map {S : Type w₁} {T : Type w₂} {S' : Type w₃} {T' : Type w₄}
    {R : S' → T' → Prop} {f : S → S'} {g : T → T'} {x : Step E A S} {y : Step E A T}
    (h : Rel R (x.map f) (y.map g)) : Rel (fun s t => R (f s) (g t)) x y := by
  cases x <;> cases y <;> cases h
  · exact .pure _
  · exact .silent ‹_›
  · exact .impure _ ‹_›

theorem Rel.map_eq {S : Type w₁} {T : Type w₂} {V : Type w₃}
    {R : S → T → Prop} {f : S → V} {g : T → V}
    {x : Step E A S} {y : Step E A T}
    (h : Rel R x y) (hfg : ∀ s t, R s t → f s = g t) :
    x.map f = y.map g := by
  cases h with
  | pure a => rfl
  | silent h => exact congrArg Step.silent (hfg _ _ h)
  | impure op h => exact congrArg (Step.impure op) (funext fun r => hfg _ _ (h r))

theorem Rel.of_map_eq {S : Type w₁} {T : Type w₂} {V : Type w₃}
    {f : S → V} {g : T → V} {x : Step E A S} {y : Step E A T}
    (h : x.map f = y.map g) : Rel (fun s t => f s = g t) x y := by
  cases x <;> cases y <;>
    simp only [Step.map, Step.pure.injEq, Step.silent.injEq, Step.impure.injEq, reduceCtorEq] at h
  · subst h; exact .pure _
  · exact .silent h
  · obtain ⟨rfl, hk⟩ := h
    exact .impure _ fun r => congrFun (eq_of_heq hk) r

theorem Rel.eq {S : Type w₁} {x y : Step E A S} (h : Rel Eq x y) : x = y := by
  cases h with
  | pure a => rfl
  | silent h => subst h; rfl
  | impure op h => exact congrArg (Step.impure op) (funext h)

end Step.Proofs
