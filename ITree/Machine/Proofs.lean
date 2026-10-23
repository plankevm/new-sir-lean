import ITree.Machine
import ITree.Step.Theorems

universe u w w'

namespace CoFree.Proofs

variable {E F : Effect.{u}} {A B : Type u}

/-! ## Positions -/

theorem atPos_initPos : ∀ m : CoFree E A, m.atPos m.initPos = m
  | ⟨_, _, _, _, _⟩ => rfl

theorem observe_atPos (m : CoFree E A) (p : m.Pos) :
    (m.atPos p).observe = (m.stepAt p).map m.atPos := by
  induction m with
  | mk S J s₀ step target ih =>
    rcases p with s | ⟨j, p⟩
    · simp only [atPos, stepAt, observe, Step.map_map]
      refine Step.map_congr (fun x => ?_) _
      rcases x with s' | j
      · rfl
      · exact (atPos_initPos (target j)).symm
    · simp only [atPos, stepAt]
      rw [ih]
      refine Eq.trans (Step.map_congr (f := (target j).atPos)
        (g := fun p' => atPos ⟨S, J, s₀, step, target⟩ (.inr ⟨j, p'⟩)) (fun _ => rfl) _) ?_
      exact (Step.map_map (fun p' => (Sum.inr ⟨j, p'⟩ : Pos ⟨S, J, s₀, step, target⟩)) _ _).symm

/-! ## Strong bisimulation -/

theorem Bisim.refl (m : CoFree E A) : Bisim m m := by
  refine ⟨Eq, ?_, rfl⟩
  intro m₁ m₂ h
  subst h
  exact Step.Rel.refl (fun _ => rfl) _

theorem Bisim.symm {m₁ m₂ : CoFree E A} : Bisim m₁ m₂ → Bisim m₂ m₁
  | ⟨R, hR, h⟩ => ⟨fun x y => R y x, fun x y hxy => (hR y x hxy).symm, h⟩

theorem Bisim.trans {m₁ m₂ m₃ : CoFree E A} : Bisim m₁ m₂ → Bisim m₂ m₃ → Bisim m₁ m₃
  | ⟨R₁, h₁, i₁⟩, ⟨R₂, h₂, i₂⟩ =>
    ⟨fun x z => ∃ y, R₁ x y ∧ R₂ y z,
     fun x z ⟨y, hxy, hyz⟩ => (h₁ x y hxy).trans (h₂ y z hyz),
     ⟨_, i₁, i₂⟩⟩

/-! ## Combinators -/

theorem observe_pure (a : A) : (pure a : CoFree E A).observe = .pure a := rfl

theorem observe_silent (m : CoFree E A) : m.silent.observe = .silent m := rfl

theorem observe_impure (op : E.Op) (k : E.Resp op → CoFree E A) :
    (impure op k).observe = .impure op k := rfl

theorem observe_branch (c : E.BrOp) (k : E.BrResp c → CoFree E A) :
    (branch c k).observe = .branch c k := rfl

theorem observe_corec {S : Type u} (f : S → Step E A S) (s : S) :
    (corec f s).observe = (f s).map (corec f) := by
  simp only [observe, corec, Step.map_map]
  rfl

theorem observe_bind (m : CoFree E A) (g : A → CoFree E B) :
    (m.bind g).observe = bindStep g m.observe := by
  obtain ⟨S, J, s₀, step, target⟩ := m
  rw [CoFree.bind.eq_1]
  simp only [observe, bindTrans]
  generalize step s₀ = st
  rcases st with a | (s | j) | ⟨op, k⟩ | ⟨c, k⟩
  · simp only [Step.map_pure, Step.map_map, bindStep]
    rfl
  · simp only [Step.map_silent, bindStep, next, startAt]
    rw [CoFree.bind.eq_1]
    rfl
  · rfl
  · simp only [Step.map_impure, bindStep]
    congr 1
    funext r
    cases k r
    · simp only [next, startAt]
      rw [CoFree.bind.eq_1]
      rfl
    · rfl
  · simp only [Step.map_branch, bindStep]
    congr 1
    funext r
    cases k r
    · simp only [next, startAt]
      rw [CoFree.bind.eq_1]
      rfl
    · rfl

theorem mapStep_map {X : Type w} {Y : Type w'} (f : E.Op → F.Op)
    (g : (op : E.Op) → F.Resp (f op) → E.Resp op) (b : Effect.BrMap E F) (h : X → Y)
    (x : Step E A X) : mapStep f g b (x.map h) = (mapStep f g b x).map h := by
  cases x <;> rfl

theorem observe_mapOps (f : E.Op → F.Op) (g : (op : E.Op) → F.Resp (f op) → E.Resp op)
    (b : Effect.BrMap E F) (m : CoFree E A) :
    (m.mapOps f g b).observe = (mapStep f g b m.observe).map (mapOps f g b) := by
  obtain ⟨S, J, s₀, step, target⟩ := m
  simp only [observe, mapOps, mapStep_map, Step.map_map]
  refine Step.map_congr (fun x => ?_) _
  cases x <;> rfl

theorem observe_iter_startAt {S : Type u} (s : S) (g : S → CoFree E (IterStep S A)) (i : S)
    (p : (g i).Pos) :
    ((iter s g).startAt ⟨i, p⟩).observe =
      match (g i).stepAt p with
      | .pure (.repeat i') => .silent (iter i' g)
      | .pure (.exit a) => .pure a
      | .silent p' => .silent ((iter s g).startAt ⟨i, p'⟩)
      | .impure op k => .impure op fun r => (iter s g).startAt ⟨i, k r⟩
      | .branch c k => .branch c fun r => (iter s g).startAt ⟨i, k r⟩ := by
  simp only [observe, iter, startAt]
  generalize (g i).stepAt p = st
  rcases st with (i' | a) | p' | ⟨op, k⟩ | ⟨c, k⟩ <;> rfl

section Interp

variable {σ : Type u}

theorem observe_interpAt_handler (h : σ → (op : E.Op) → CoFree F (σ × E.Resp op))
    (b : Effect.BrMap E F) (m : CoFree E A) (op : E.Op) (k : E.Resp op → m.State ⊕ m.Jump) (s : σ)
    (p : (h s op).Pos) :
    (interpAt h b m (.handler op k s p)).observe =
      match (h s op).stepAt p with
      | .pure (s', r) => .silent (interpState h b s' (m.next (k r)))
      | .silent p' => .silent (interpAt h b m (.handler op k s p'))
      | .impure op' k' => .impure op' fun r => interpAt h b m (.handler op k s (k' r))
      | .branch c k' => .branch c fun r => interpAt h b m (.handler op k s (k' r)) := by
  obtain ⟨S, J, s₀, step, target⟩ := m
  simp only [interpAt, observe, interpHandle]
  generalize (h s op).stepAt p = st
  rcases st with ⟨s', r⟩ | p' | ⟨op', k'⟩ | ⟨c, k'⟩
  · simp only [Step.map]
    cases k r <;> rfl
  · rfl
  · rfl
  · rfl

theorem observe_interpState (h : σ → (op : E.Op) → CoFree F (σ × E.Resp op))
    (b : Effect.BrMap E F) (s : σ) (m : CoFree E A) :
    (interpState h b s m).observe =
      match m.step m.initial with
      | .pure a => .pure (s, a)
      | .silent y => .silent (interpState h b s (m.next y))
      | .impure op k => (interpAt h b m (.handler op k s (h s op).initPos)).observe
      | .branch c k => .branch (b.op c) fun r => interpState h b s (m.next (k (b.resp c r))) := by
  obtain ⟨S, J, s₀, step, target⟩ := m
  simp only [interpState, interpAt, observe]
  generalize step s₀ = st
  rcases st with a | (x | j) | ⟨op, k⟩ | ⟨c, k⟩
  · rfl
  · rfl
  · rfl
  · exact Step.map_congr (fun x => by cases x <;> rfl) _
  · simp only [Step.map_branch]
    congr 1
    funext r
    cases k (b.resp c r) <;> rfl

end Interp

theorem observe_fixFrom_startAt {I O : Type u} (body : I → CoFree (Effect.Call I O ⊕ₑ E) O)
    (t : CoFree (Effect.Call I O ⊕ₑ E) O) (c : Option I) (p : (fixCode body t c).Pos)
    (stack : List (FixFrame body t)) :
    ((fixFrom body t).startAt ⟨c, p, stack⟩).observe =
      match (fixCode body t c).stepAt p, stack with
      | .pure o, [] => .pure o
      | .pure o, ⟨c', k⟩ :: rest => .silent ((fixFrom body t).startAt ⟨c', k o, rest⟩)
      | .silent p', stack => .silent ((fixFrom body t).startAt ⟨c, p', stack⟩)
      | .impure (.inl i) k, stack =>
        .silent ((fixFrom body t).startAt ⟨some i, (body i).initPos, ⟨c, k⟩ :: stack⟩)
      | .impure (.inr op) k, stack => .impure op fun r => (fixFrom body t).startAt ⟨c, k r, stack⟩
      | .branch (.inl b) _, _ => nomatch b
      | .branch (.inr b) k, stack => .branch b fun r => (fixFrom body t).startAt ⟨c, k r, stack⟩ := by
  simp only [observe, fixFrom, startAt]
  generalize (fixCode body t c).stepAt p = st
  rcases st with o | p' | ⟨op | op, k⟩ | ⟨b | b, k⟩
  · cases stack <;> rfl
  · rfl
  · rfl
  · rfl
  · exact nomatch b
  · rfl

end CoFree.Proofs
