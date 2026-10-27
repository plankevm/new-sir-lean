import ITree.Step.Proofs

universe u w₁ w₂ w₃

namespace Step

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u}

@[simp] theorem map_pure {S : Type w₁} {T : Type w₂} (f : S → T) (a : A) :
    (Step.pure a : Step E N A S).map f = .pure a :=
  Proofs.map_pure f a

@[simp] theorem map_silent {S : Type w₁} {T : Type w₂} (f : S → T) (s : S) :
    (Step.silent s : Step E N A S).map f = .silent (f s) :=
  Proofs.map_silent f s

@[simp] theorem map_impure {S : Type w₁} {T : Type w₂} (f : S → T) (op : E.Op)
    (k : E.Resp op → S) : (Step.impure op k : Step E N A S).map f = .impure op fun r => f (k r) :=
  Proofs.map_impure f op k

@[simp] theorem map_branch {S : Type w₁} {T : Type w₂} (f : S → T) (c : N.Op)
    (k : N.Resp c → S) : (Step.branch c k : Step E N A S).map f = .branch c fun r => f (k r) :=
  Proofs.map_branch f c k

theorem map_map {S : Type w₁} {T : Type w₂} {U : Type w₃} (f : S → T) (g : T → U)
    (x : Step E N A S) : (x.map f).map g = x.map fun s => g (f s) :=
  Proofs.map_map f g x

theorem map_congr {S : Type w₁} {T : Type w₂} {f g : S → T} (h : ∀ s, f s = g s)
    (x : Step E N A S) : x.map f = x.map g :=
  Proofs.map_congr h x

end Step
