import ITree.Machine.Proofs

universe u w w'

namespace CoFree

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A B : Type u}

/-! ## Positions -/

theorem atPos_initPos : ∀ m : CoFree E N A, m.atPos m.initPos = m :=
  Proofs.atPos_initPos

theorem observe_atPos (m : CoFree E N A) (p : m.Pos) :
    (m.atPos p).observe = (m.stepAt p).map m.atPos :=
  Proofs.observe_atPos m p

/-! ## Combinators -/

@[simp] theorem observe_pure (a : A) : (pure a : CoFree E N A).observe = .pure a :=
  Proofs.observe_pure a

@[simp] theorem observe_silent (m : CoFree E N A) : m.silent.observe = .silent m :=
  Proofs.observe_silent m

@[simp] theorem observe_perform (op : E.Op) :
    (perform op : CoFree E N _).observe = .impure op pure :=
  Proofs.observe_perform op

@[simp] theorem observe_branch (c : N.Op) : (branch c : CoFree E N _).observe = .branch c pure :=
  Proofs.observe_branch c

theorem observe_corec {S : Type u} (f : S → Step E N A S) (s : S) :
    (corec f s).observe = (f s).map (corec f) :=
  Proofs.observe_corec f s

theorem observe_bind (m : CoFree E N A) (g : A → CoFree E N B) :
    (m.bind g).observe = bindStep g m.observe :=
  Proofs.observe_bind m g

theorem mapStep_map {X : Type w} {Y : Type w'} (f : E.Op → F.Op)
    (g : (op : E.Op) → F.Resp (f op) → E.Resp op) (b : NonDeterminism.Map N M) (h : X → Y)
    (x : Step E N A X) : mapStep f g b (x.map h) = (mapStep f g b x).map h :=
  Proofs.mapStep_map f g b h x

theorem observe_mapOps (f : E.Op → F.Op) (g : (op : E.Op) → F.Resp (f op) → E.Resp op)
    (b : NonDeterminism.Map N M) (m : CoFree E N A) :
    (m.mapOps f g b).observe = (mapStep f g b m.observe).map (mapOps f g b) :=
  Proofs.observe_mapOps f g b m

theorem observe_iter_startAt {S : Type u} (s : S) (g : S → CoFree E N (IterStep S A)) (i : S)
    (p : (g i).Pos) :
    ((iter s g).startAt ⟨i, p⟩).observe =
      match (g i).stepAt p with
      | .pure (.repeat i') => .silent (iter i' g)
      | .pure (.exit a) => .pure a
      | .silent p' => .silent ((iter s g).startAt ⟨i, p'⟩)
      | .impure op k => .impure op fun r => (iter s g).startAt ⟨i, k r⟩
      | .branch c k => .branch c fun r => (iter s g).startAt ⟨i, k r⟩ :=
  Proofs.observe_iter_startAt s g i p

theorem observe_fixFrom_startAt {I O : Type u} (body : I → CoFree (Effect.Call I O ⊕ₑ E) N O)
    (t : CoFree (Effect.Call I O ⊕ₑ E) N O) (c : Option I) (p : (fixCode body t c).Pos)
    (stack : List (FixFrame body t)) :
    ((fixFrom body t).startAt ⟨c, p, stack⟩).observe =
      match (fixCode body t c).stepAt p, stack with
      | .pure o, [] => .pure o
      | .pure o, ⟨c', k⟩ :: rest => .silent ((fixFrom body t).startAt ⟨c', k o, rest⟩)
      | .silent p', stack => .silent ((fixFrom body t).startAt ⟨c, p', stack⟩)
      | .impure (.inl i) k, stack =>
        .silent ((fixFrom body t).startAt ⟨some i, (body i).initPos, ⟨c, k⟩ :: stack⟩)
      | .impure (.inr op) k, stack => .impure op fun r => (fixFrom body t).startAt ⟨c, k r, stack⟩
      | .branch b k, stack => .branch b fun r => (fixFrom body t).startAt ⟨c, k r, stack⟩ :=
  Proofs.observe_fixFrom_startAt body t c p stack

end CoFree
