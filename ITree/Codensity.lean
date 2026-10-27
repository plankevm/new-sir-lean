import ITree.Program

universe u

namespace CoFree

/-- Continuation-passing wrapper around `CoFree`. Binds associate to the right when lowered,
so left-nested binds run in linear time. -/
structure Cod (E : Effect.{u}) (N : NonDeterminism.{u}) (A : Type u) : Type (u+1) where
  run : {R : Type u} → (A → CoFree E N R) → CoFree E N R

namespace Cod

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A B : Type u}

instance : Monad (Cod.{u} E N) where
  pure a := ⟨fun k => k a⟩
  bind x f := ⟨fun k => x.run fun a => (f a).run k⟩

def lift (m : CoFree E N A) : Cod E N A :=
  ⟨fun k => m.bind k⟩

def lower (x : Cod E N A) : CoFree E N A :=
  x.run pure

def perform (op : E.Op) : Cod E N (E.Resp op) :=
  lift (CoFree.perform op)

end Cod

end CoFree
