import ITree.Program

universe u

namespace CoFree

/-- Continuation-passing wrapper around `CoFree`. Binds associate to the right when lowered,
so left-nested binds run in linear time. -/
structure Cod (E : Effect.{u}) (A : Type u) : Type (u+1) where
  run : {R : Type u} → (A → CoFree E R) → CoFree E R

namespace Cod

variable {E : Effect.{u}} {A B : Type u}

instance : Monad (Cod.{u} E) where
  pure a := ⟨fun k => k a⟩
  bind x f := ⟨fun k => x.run fun a => (f a).run k⟩

def lift (m : CoFree E A) : Cod E A :=
  ⟨fun k => m.bind k⟩

def lower (x : Cod E A) : CoFree E A :=
  x.run pure

def perform (op : E.Op) : Cod E (E.Resp op) :=
  lift (CoFree.perform op)

end Cod

end CoFree
