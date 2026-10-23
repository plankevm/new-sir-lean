import ITree.Step.Proofs

universe u w₁ w₂ w₃ w₄

namespace Step

variable {E : Effect.{u}} {A : Type u}

@[simp] theorem map_pure {S : Type w₁} {T : Type w₂} (f : S → T) (a : A) :
    (Step.pure a : Step E A S).map f = .pure a :=
  Proofs.map_pure f a

@[simp] theorem map_silent {S : Type w₁} {T : Type w₂} (f : S → T) (s : S) :
    (Step.silent s : Step E A S).map f = .silent (f s) :=
  Proofs.map_silent f s

@[simp] theorem map_impure {S : Type w₁} {T : Type w₂} (f : S → T) (op : E.Op)
    (k : E.Resp op → S) : (Step.impure op k : Step E A S).map f = .impure op fun r => f (k r) :=
  Proofs.map_impure f op k

@[simp] theorem map_br {S : Type w₁} {T : Type w₂} (f : S → T) (c : E.BrOp)
    (k : E.BrResp c → S) : (Step.br c k : Step E A S).map f = .br c fun r => f (k r) :=
  Proofs.map_br f c k

theorem map_map {S : Type w₁} {T : Type w₂} {U : Type w₃} (f : S → T) (g : T → U)
    (x : Step E A S) : (x.map f).map g = x.map fun s => g (f s) :=
  Proofs.map_map f g x

theorem map_congr {S : Type w₁} {T : Type w₂} {f g : S → T} (h : ∀ s, f s = g s)
    (x : Step E A S) : x.map f = x.map g :=
  Proofs.map_congr h x

theorem Rel.refl {S : Type w₁} {R : S → S → Prop} (hR : ∀ s, R s s) :
    ∀ x : Step E A S, Rel R x x :=
  Proofs.Rel.refl hR

theorem Rel.symm {S : Type w₁} {T : Type w₂} {R : S → T → Prop}
    {x : Step E A S} {y : Step E A T} (h : Rel R x y) : Rel (fun t s => R s t) y x :=
  Proofs.Rel.symm h

theorem Rel.trans {S : Type w₁} {T : Type w₂} {U : Type w₃}
    {R₁ : S → T → Prop} {R₂ : T → U → Prop}
    {x : Step E A S} {y : Step E A T} {z : Step E A U}
    (h₁ : Rel R₁ x y) (h₂ : Rel R₂ y z) :
    Rel (fun s u => ∃ t, R₁ s t ∧ R₂ t u) x z :=
  Proofs.Rel.trans h₁ h₂

theorem Rel.mono {S : Type w₁} {T : Type w₂} {R R' : S → T → Prop}
    {x : Step E A S} {y : Step E A T}
    (h : Rel R x y) (hR : ∀ s t, R s t → R' s t) : Rel R' x y :=
  Proofs.Rel.mono h hR

theorem Rel.map {S : Type w₁} {T : Type w₂} {S' : Type w₃} {T' : Type w₄}
    {R : S → T → Prop} {R' : S' → T' → Prop} {f : S → S'} {g : T → T'}
    {x : Step E A S} {y : Step E A T}
    (h : Rel R x y) (hfg : ∀ s t, R s t → R' (f s) (g t)) :
    Rel R' (x.map f) (y.map g) :=
  Proofs.Rel.map h hfg

theorem Rel.of_map {S : Type w₁} {T : Type w₂} {S' : Type w₃} {T' : Type w₄}
    {R : S' → T' → Prop} {f : S → S'} {g : T → T'} {x : Step E A S} {y : Step E A T}
    (h : Rel R (x.map f) (y.map g)) : Rel (fun s t => R (f s) (g t)) x y :=
  Proofs.Rel.of_map h

theorem Rel.map_eq {S : Type w₁} {T : Type w₂} {V : Type w₃}
    {R : S → T → Prop} {f : S → V} {g : T → V}
    {x : Step E A S} {y : Step E A T}
    (h : Rel R x y) (hfg : ∀ s t, R s t → f s = g t) :
    x.map f = y.map g :=
  Proofs.Rel.map_eq h hfg

theorem Rel.of_map_eq {S : Type w₁} {T : Type w₂} {V : Type w₃}
    {f : S → V} {g : T → V} {x : Step E A S} {y : Step E A T}
    (h : x.map f = y.map g) : Rel (fun s t => f s = g t) x y :=
  Proofs.Rel.of_map_eq h

theorem Rel.eq {S : Type w₁} {x y : Step E A S} (h : Rel Eq x y) : x = y :=
  Proofs.Rel.eq h

end Step
