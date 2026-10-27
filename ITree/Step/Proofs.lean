import ITree.Step

universe u w₁ w₂ w₃

namespace Step.Proofs

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u}

theorem map_pure {S : Type w₁} {T : Type w₂} (f : S → T) (a : A) :
    (Step.pure a : Step E N A S).map f = .pure a := rfl

theorem map_silent {S : Type w₁} {T : Type w₂} (f : S → T) (s : S) :
    (Step.silent s : Step E N A S).map f = .silent (f s) := rfl

theorem map_impure {S : Type w₁} {T : Type w₂} (f : S → T) (op : E.Op)
    (k : E.Resp op → S) : (Step.impure op k : Step E N A S).map f = .impure op fun r => f (k r) :=
  rfl

theorem map_branch {S : Type w₁} {T : Type w₂} (f : S → T) (c : N.Op)
    (k : N.Resp c → S) : (Step.branch c k : Step E N A S).map f = .branch c fun r => f (k r) :=
  rfl

theorem map_map {S : Type w₁} {T : Type w₂} {U : Type w₃} (f : S → T) (g : T → U)
    (x : Step E N A S) : (x.map f).map g = x.map fun s => g (f s) := by
  cases x <;> rfl

theorem map_congr {S : Type w₁} {T : Type w₂} {f g : S → T} (h : ∀ s, f s = g s)
    (x : Step E N A S) : x.map f = x.map g := by
  obtain rfl : f = g := funext h
  rfl

end Step.Proofs
