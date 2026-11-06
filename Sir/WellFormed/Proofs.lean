import Sir.WellFormed
import Sir.Eval
import Sir.Layout.Theorems
import ITree.Machine.Theorems
import ITree.Reaches.Theorems

open Host CoFree

open Lean Elab Term Meta in
elab "arrayMapM_map%" : term =>
  mkConstWithFreshMVarLevels (Name.mkNum `_private.Init.Data.Array.Basic 0 ++ `Array.mapM.map)

open Lean Elab Term Meta in
elab "arrayMapM_map_eq%" : term => do
  let some #[eq] ← getEqnsFor? (Name.mkNum `_private.Init.Data.Array.Basic 0 ++ `Array.mapM.map)
    | throwError "unexpected equations for Array.mapM.map"
  mkConstWithFreshMVarLevels eq

namespace Sir.Proofs

universe u

section Good

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {A B : Type u}

def Closed (Bad : E.Op → Prop) (Ok : (op : E.Op) → E.Resp op → Prop) (Q : A → Prop)
    (J : CoFree E N A → Prop) (m : CoFree E N A) : Prop :=
  match m.observe with
  | .pure a => Q a
  | .silent m' => J m'
  | .impure op k => ¬Bad op ∧ ∀ r, Ok op r → J (k r)
  | .branch _ k => ∀ r, J (k r)

def Good (Bad : E.Op → Prop) (Ok : (op : E.Op) → E.Resp op → Prop) (Q : A → Prop)
    (m : CoFree E N A) : Prop :=
  ∃ J : CoFree E N A → Prop, J m ∧ ∀ x, J x → Closed Bad Ok Q J x

variable {Bad : E.Op → Prop} {Ok : (op : E.Op) → E.Resp op → Prop}

lemma closed_mono {Q : A → Prop} {J J' : CoFree E N A → Prop} (hJ : ∀ x, J x → J' x)
    {m : CoFree E N A} (h : Closed Bad Ok Q J m) : Closed Bad Ok Q J' m := by
  unfold Closed at *
  split at h <;> simp_all

lemma closed_congr {Q : A → Prop} {J : CoFree E N A → Prop} {m m' : CoFree E N A}
    (ho : m.observe = m'.observe) : Closed Bad Ok Q J m ↔ Closed Bad Ok Q J m' := by
  unfold Closed; rw [ho]

lemma good_unfold {Q : A → Prop} {m : CoFree E N A} (h : Good Bad Ok Q m) :
    Closed Bad Ok Q (Good Bad Ok Q) m := by
  obtain ⟨J, hm, hJ⟩ := h
  exact closed_mono (fun x hx => ⟨J, hx, hJ⟩) (hJ m hm)

lemma good_fold {Q : A → Prop} {m : CoFree E N A} (h : Closed Bad Ok Q (Good Bad Ok Q) m) :
    Good Bad Ok Q m := by
  refine ⟨fun x => x = m ∨ Good Bad Ok Q x, .inl rfl, fun x hx => ?_⟩
  rcases hx with rfl | hx
  · exact closed_mono (fun _ => .inr) h
  · exact closed_mono (fun _ => .inr) (good_unfold hx)

lemma good_congr {Q : A → Prop} {m m' : CoFree E N A} (ho : m.observe = m'.observe)
    (h : Good Bad Ok Q m) : Good Bad Ok Q m' :=
  good_fold ((closed_congr ho).1 (good_unfold h))

lemma good_mono {Q Q' : A → Prop} (hQ : ∀ a, Q a → Q' a) {m : CoFree E N A}
    (h : Good Bad Ok Q m) : Good Bad Ok Q' m := by
  obtain ⟨J, hm, hJ⟩ := h
  refine ⟨J, hm, fun x hx => ?_⟩
  have := hJ x hx
  unfold Closed at *
  split at this <;> simp_all

lemma good_pure {Q : A → Prop} {a : A} (h : Q a) : Good Bad Ok Q (CoFree.pure a : CoFree E N A) :=
  good_fold (by unfold Closed; rw [observe_pure]; exact h)

lemma good_perform {op : E.Op} {Q : E.Resp op → Prop} (hb : ¬Bad op) (hq : ∀ r, Ok op r → Q r) :
    Good Bad Ok Q (perform op : CoFree E N _) :=
  good_fold (by
    unfold Closed; rw [observe_perform]
    exact ⟨hb, fun r hr => good_pure (hq r hr)⟩)

lemma good_bind {Q₁ : A → Prop} {Q₂ : B → Prop} {m : CoFree E N A} {g : A → CoFree E N B}
    (hm : Good Bad Ok Q₁ m) (hg : ∀ a, Q₁ a → Good Bad Ok Q₂ (g a)) :
    Good Bad Ok Q₂ (m >>= g) := by
  refine ⟨fun x => (∃ m₀, Good Bad Ok Q₁ m₀ ∧ x = m₀.bind g) ∨ Good Bad Ok Q₂ x,
    .inl ⟨m, hm, rfl⟩, fun x hx => ?_⟩
  rcases hx with ⟨m₀, h₀, rfl⟩ | hx
  · have h := good_unfold h₀
    unfold Closed at h ⊢
    rw [observe_bind]
    cases ho : m₀.observe with
    | pure a =>
      rw [ho] at h
      have := good_unfold (hg a h)
      unfold Closed at this
      simp only [bindStep]
      split at this <;> simp_all
    | silent m' =>
      rw [ho] at h
      exact .inl ⟨_, h, rfl⟩
    | impure op k =>
      rw [ho] at h
      exact ⟨h.1, fun r hr => .inl ⟨_, h.2 r hr, rfl⟩⟩
    | branch c k =>
      rw [ho] at h
      exact fun r => .inl ⟨_, h r, rfl⟩
  · exact closed_mono (fun _ => .inr) (good_unfold hx)

lemma good_bind' {Q₁ : A → Prop} {Q₂ : B → Prop} {m : CoFree E N A} {g : A → CoFree E N B}
    (hm : Good Bad Ok Q₁ m) (hg : ∀ a, Q₁ a → Good Bad Ok Q₂ (g a)) :
    Good Bad Ok Q₂ (m.bind g) := good_bind hm hg

lemma good_mapOps {F : Effect.{u}} {M : NonDeterminism.{u}} {Bad' : F.Op → Prop}
    {Ok' : (op : F.Op) → F.Resp op → Prop} {Q : A → Prop} (e : Effect.Map E F)
    (nd : NonDeterminism.Map N M) (hb : ∀ op, Bad' (e.op op) → Bad op)
    (hok : ∀ op r, Ok' (e.op op) r → Ok op (e.resp op r)) {m : CoFree E N A}
    (h : Good Bad Ok Q m) : Good Bad' Ok' Q (m.mapOps e nd) := by
  refine ⟨fun x => ∃ m₀, Good Bad Ok Q m₀ ∧ x = m₀.mapOps e nd, ⟨m, h, rfl⟩, ?_⟩
  rintro _ ⟨m₀, h₀, rfl⟩
  have h := good_unfold h₀
  unfold Closed at h ⊢
  rw [observe_mapOps]
  cases ho : m₀.observe with
  | pure a => rw [ho] at h; exact h
  | silent m' => rw [ho] at h; exact ⟨_, h, rfl⟩
  | impure op k =>
    rw [ho] at h
    exact ⟨fun hb' => h.1 (hb op hb'), fun r hr => ⟨_, h.2 _ (hok op r hr), rfl⟩⟩
  | branch c k => rw [ho] at h; exact fun r => ⟨_, h _, rfl⟩

lemma good_iter {S : Type u} {Q : A → Prop} (Inv : S → Prop) (g : S → CoFree E N (IterStep S A))
    (hg : ∀ s, Inv s → Good Bad Ok (fun | .repeat s' => Inv s' | .exit a => Q a) (g s))
    {s₀ : S} (h₀ : Inv s₀) : Good Bad Ok Q (iter s₀ g) := by
  refine ⟨fun x => ∃ i p, x = (iter s₀ g).startAt ⟨i, p⟩ ∧ Inv i ∧
      Good Bad Ok (fun | .repeat s' => Inv s' | .exit a => Q a) ((g i).atPos p),
    ⟨s₀, (g s₀).initPos, rfl, h₀, by rw [atPos_initPos]; exact hg s₀ h₀⟩, ?_⟩
  rintro _ ⟨i, p, rfl, hi, hp⟩
  have h := good_unfold hp
  unfold Closed at h ⊢
  rw [observe_atPos] at h
  rw [observe_iter_startAt]
  cases hs : (g i).stepAt p with
  | pure x =>
    rw [hs] at h
    cases x with
    | «repeat» s' =>
      exact ⟨s', (g s').initPos, rfl, h, by rw [atPos_initPos]; exact hg s' h⟩
    | exit a => exact h
  | silent p' => rw [hs] at h; exact ⟨i, p', rfl, hi, h⟩
  | impure op k => rw [hs] at h; exact ⟨h.1, fun r hr => ⟨i, k r, rfl, hi, h.2 r hr⟩⟩
  | branch c k => rw [hs] at h; exact fun r => ⟨i, k r, rfl, hi, h r⟩

lemma good_loop {β : Type u} {Q : β → Prop} (Inv : β → Prop)
    (f : Unit → β → CoFree E N (ForInStep β))
    (hf : ∀ b, Inv b → Good Bad Ok (fun | .yield b' => Inv b' | .done b' => Q b') (f () b))
    {b₀ : β} (h₀ : Inv b₀) : Good Bad Ok Q (forIn Lean.Loop.mk b₀ f) :=
  good_iter Inv _ (fun b hb => good_bind (hf b hb) fun x hx => by
    cases x <;> exact good_pure hx) h₀

lemma good_forIn_list {α β : Type u} {Q : β → Prop} (Inv : List α → β → Prop)
    (f : α → β → CoFree E N (ForInStep β))
    (hf : ∀ a l b, Inv (a :: l) b →
      Good Bad Ok (fun | .yield b' => Inv l b' | .done b' => Q b') (f a b))
    (hnil : ∀ b, Inv [] b → Q b) :
    ∀ (l : List α) (b : β), Inv l b → Good Bad Ok Q (forIn l b f)
  | [], b, h => by rw [List.forIn_nil]; exact good_pure (hnil b h)
  | a :: l, b, h => by
    rw [List.forIn_cons]
    exact good_bind (hf a l b h) fun
      | .yield b', h' => good_forIn_list Inv f hf hnil l b' h'
      | .done _, h' => good_pure h'

lemma good_forIn_array {α β : Type u} {Q : β → Prop} (Inv : Nat → β → Prop)
    (xs : Array α) (f : α → β → CoFree E N (ForInStep β))
    (hf : ∀ i (h : i < xs.size) b, Inv i b →
      Good Bad Ok (fun | .yield b' => Inv (i + 1) b' | .done b' => Q b') (f xs[i] b))
    (hend : ∀ b, Inv xs.size b → Q b) {b : β} (h₀ : Inv 0 b) : Good Bad Ok Q (forIn xs b f) := by
  rw [← Array.forIn_toList]
  refine good_forIn_list (fun l b => ∃ i, i ≤ xs.size ∧ l = xs.toList.drop i ∧ Inv i b) f ?_ ?_
    _ b ⟨0, by omega, by simp, h₀⟩
  · rintro a l b ⟨i, -, hl, hi⟩
    have hlt : i < xs.size := by
      have := congrArg List.length hl; simp at this; omega
    have ha : xs[i] = a := by
      have := congrArg List.head? hl
      simp [List.head?_drop, hlt] at this; exact this.symm
    subst ha
    refine good_mono (fun x hx => ?_) (hf i hlt b hi)
    cases x with
    | yield b' =>
      refine ⟨i + 1, hlt, ?_, hx⟩
      have := congrArg List.tail hl
      simp [List.tail_drop] at this; exact this
    | done b' => exact hx
  · rintro b ⟨i, hle, hl, hi⟩
    have : i = xs.size := by
      have := congrArg List.length hl; simp at this; omega
    subst this
    exact hend b hi

section Fix

variable {I O : Type u}

def RecBad (Pre : I → Prop) (Bad : E.Op → Prop) : (Effect.Call I O ⊕ₑ E).Op → Prop
  | .inl i => ¬Pre i
  | .inr op => Bad op

def RecOk (Post : I → O → Prop) (Ok : (op : E.Op) → E.Resp op → Prop) :
    (op : (Effect.Call I O ⊕ₑ E).Op) → (Effect.Call I O ⊕ₑ E).Resp op → Prop
  | .inl i => fun o => Post i o
  | .inr op => fun r => Ok op r

variable {Pre : I → Prop} {Post : I → O → Prop} {body : I → CoFree (Effect.Call I O ⊕ₑ E) N O}
  {t : CoFree (Effect.Call I O ⊕ₑ E) N O}

def StackOK (Bad : E.Op → Prop) (Ok : (op : E.Op) → E.Resp op → Prop) (Pre : I → Prop)
    (Post : I → O → Prop) (Q : O → Prop) : (O → Prop) → List (FixFrame body t) → Prop
  | R, [] => ∀ o, R o → Q o
  | R, fr :: rest => ∃ R', (∀ o, R o → Good (RecBad Pre Bad) (RecOk Post Ok) R'
      ((fixCode body t fr.code).atPos (fr.resume o))) ∧ StackOK Bad Ok Pre Post Q R' rest

lemma good_fixFrom {Q : O → Prop}
    (hbody : ∀ i, Pre i → Good (RecBad Pre Bad) (RecOk Post Ok) (Post i) (body i))
    {R : O → Prop} (ht : Good (RecBad Pre Bad) (RecOk Post Ok) R t) (hR : ∀ o, R o → Q o) :
    Good Bad Ok Q (fixFrom body t) := by
  refine ⟨fun x => ∃ c p stack, x = (fixFrom body t).startAt ⟨c, p, stack⟩ ∧ ∃ R,
      Good (RecBad Pre Bad) (RecOk Post Ok) R ((fixCode body t c).atPos p) ∧
      StackOK Bad Ok Pre Post Q R stack,
    ⟨none, t.initPos, [], rfl, R, by simp only [fixCode, atPos_initPos]; exact ht, hR⟩, ?_⟩
  rintro _ ⟨c, p, stack, rfl, R, hp, hs⟩
  have h := good_unfold hp
  unfold Closed at h ⊢
  rw [observe_atPos] at h
  rw [observe_fixFrom_startAt]
  cases hst : (fixCode body t c).stepAt p with
  | pure o =>
    rw [hst] at h
    cases stack with
    | nil => exact hs o h
    | cons fr rest =>
      obtain ⟨R', hR', hrest⟩ := hs
      exact ⟨fr.code, fr.resume o, rest, rfl, R', hR' o h, hrest⟩
  | silent p' => rw [hst] at h; exact ⟨c, p', stack, rfl, R, h, hs⟩
  | impure op k =>
    rw [hst] at h
    cases op with
    | inl i =>
      have hi : Pre i := Classical.byContradiction h.1
      exact ⟨some i, (body i).initPos, ⟨c, k⟩ :: stack, rfl, Post i,
        by simp only [fixCode, atPos_initPos]; exact hbody i hi, R, fun o ho => h.2 o ho, hs⟩
    | inr op => exact ⟨h.1, fun r hr => ⟨c, k r, stack, rfl, R, h.2 r hr, hs⟩⟩
  | branch b k => rw [hst] at h; exact fun r => ⟨c, k r, stack, rfl, R, h r, hs⟩

lemma good_fix
    (f : (I → CoFree (Effect.Rec I O E) N O) → I → CoFree (Effect.Rec I O E) N O)
    (hbody : ∀ i, Pre i → Good (RecBad Pre Bad) (RecOk Post Ok) (Post i)
      (f (fun j => perform (E := Effect.Rec I O E) (.inl j)) i))
    {i : I} (hi : Pre i) : Good Bad Ok (Post i) (CoFree.fix f i) :=
  good_fixFrom hbody (hbody i hi) fun _ h => h

end Fix

end Good

section Outcome

variable {E F : Effect.{u}} {N M : NonDeterminism.{u}} {A B : Type u}

lemma good_reaches {Bad : E.Op → Prop} {Q : A → Prop} {m m' : CoFree E N A}
    (h : Good Bad (fun _ _ => True) Q m) (hr : Reaches m m') :
    ∀ op k, m'.observe = .impure op k → ¬Bad op := by
  induction hr with
  | refl =>
    intro op k ho
    have := good_unfold h
    unfold Closed at this; rw [ho] at this; exact this.1
  | silent ho _ ih =>
    have := good_unfold h
    unfold Closed at this; rw [ho] at this; exact ih this
  | impure r ho _ ih =>
    have := good_unfold h
    unfold Closed at this; rw [ho] at this; exact ih (this.2 r trivial)
  | branch r ho _ ih =>
    have := good_unfold h
    unfold Closed at this; rw [ho] at this; exact ih (this r)

lemma hasOutcome_congr {m m' : CoFree E N A} {o : Outcome E A} (ho : m.observe = m'.observe)
    (h : HasOutcome m o) : HasOutcome m' o := by
  cases h with
  | res h => exact .res (ho ▸ h)
  | terminal hr h => exact .terminal hr (ho ▸ h)
  | silent h h' => exact .silent h (ho ▸ h')
  | branch h h' => exact .branch h (ho ▸ h')
  | impure h h' => exact .impure h (ho ▸ h')

lemma hasOutcome_of_reaches {m m' : CoFree E N A} {o : Outcome E A} (hr : Reaches m m')
    (h : HasOutcome m' o) : HasOutcome m o := by
  induction hr with
  | refl => exact h
  | silent ho _ ih => exact .silent (ih h) ho
  | impure r ho _ ih => exact .impure (ih h) ⟨_, _, ho, r, rfl⟩
  | branch r ho _ ih => exact .branch (ih h) ⟨_, _, ho, r, rfl⟩

lemma hasOutcome_bind {m : CoFree E N A} {g : A → CoFree E N B} {b : B}
    (h : HasOutcome (m.bind g) (.res b)) : ∃ a, HasOutcome m (.res a) ∧ HasOutcome (g a) (.res b) := by
  generalize hM : m.bind g = X at h
  generalize ho : (Outcome.res b : Outcome E B) = o at h
  induction h generalizing m with
  | res hv =>
    subst hM; cases ho
    rw [observe_bind] at hv
    cases hm : m.observe with
    | pure a => rw [hm] at hv; exact ⟨_, .res hm, .res hv⟩
    | silent => rw [hm] at hv; cases hv
    | impure => rw [hm] at hv; cases hv
    | branch => rw [hm] at hv; cases hv
  | terminal => cases ho
  | @silent X X' o' hX' hs ih =>
    subst hM; subst ho
    cases hm : m.observe with
    | pure a =>
      exact ⟨a, .res hm, hasOutcome_congr (by rw [observe_bind, hm]; rfl) (.silent hX' hs)⟩
    | silent n =>
      rw [observe_bind, hm] at hs
      injection hs with hs
      obtain ⟨a, h₁, h₂⟩ := ih hs rfl
      exact ⟨a, .silent h₁ hm, h₂⟩
    | impure => rw [observe_bind, hm] at hs; cases hs
    | branch => rw [observe_bind, hm] at hs; cases hs
  | @branch X X' o' hX' hs ih =>
    subst hM; subst ho
    cases hm : m.observe with
    | pure a =>
      exact ⟨a, .res hm, hasOutcome_congr (by rw [observe_bind, hm]; rfl) (.branch hX' hs)⟩
    | branch c k' =>
      obtain ⟨br, k, hs, r, rfl⟩ := hs
      rw [observe_bind, hm] at hs
      simp only [bindStep] at hs
      injection hs with hc hk
      subst hc; cases hk
      obtain ⟨a, h₁, h₂⟩ := ih rfl rfl
      exact ⟨a, .branch h₁ ⟨_, _, hm, r, rfl⟩, h₂⟩
    | silent => obtain ⟨_, _, hs, _⟩ := hs; rw [observe_bind, hm] at hs; cases hs
    | impure => obtain ⟨_, _, hs, _⟩ := hs; rw [observe_bind, hm] at hs; cases hs
  | @impure X X' o' hX' hs ih =>
    subst hM; subst ho
    cases hm : m.observe with
    | pure a =>
      exact ⟨a, .res hm, hasOutcome_congr (by rw [observe_bind, hm]; rfl) (.impure hX' hs)⟩
    | impure op' k' =>
      obtain ⟨op, k, hs, r, rfl⟩ := hs
      rw [observe_bind, hm] at hs
      simp only [bindStep] at hs
      injection hs with hc hk
      subst hc; cases hk
      obtain ⟨a, h₁, h₂⟩ := ih rfl rfl
      exact ⟨a, .impure h₁ ⟨_, _, hm, r, rfl⟩, h₂⟩
    | silent => obtain ⟨_, _, hs, _⟩ := hs; rw [observe_bind, hm] at hs; cases hs
    | branch => obtain ⟨_, _, hs, _⟩ := hs; rw [observe_bind, hm] at hs; cases hs

lemma reaches_trans {m₁ m₂ m₃ : CoFree E N A} (h₁ : Reaches m₁ m₂) (h₂ : Reaches m₂ m₃) :
    Reaches m₁ m₃ := by
  induction h₁ with
  | refl => exact h₂
  | silent ho _ ih => exact .silent ho (ih h₂)
  | impure r ho _ ih => exact .impure r ho (ih h₂)
  | branch r ho _ ih => exact .branch r ho (ih h₂)

def IsSucc {X : Type u} (s : Step E N A X) (x : X) : Prop :=
  s = .silent x ∨ (∃ op k r, s = .impure op k ∧ k r = x) ∨ (∃ c k r, s = .branch c k ∧ k r = x)

def Faithful {σ : Type u} (h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X)) : Prop :=
  ∀ {X : Type u} st (s : Step E N A X),
    (∀ x, h st s = .silent x → IsSucc s x.2) ∧
    (∀ op k r, h st s = .impure op k → IsSucc s (k r).2) ∧
    (∀ c k r, h st s = .branch c k → IsSucc s (k r).2)

lemma reaches_next {m : CoFree E N A} {x : m.State ⊕ m.Jump} (hx : IsSucc (m.step m.initial) x) :
    Reaches m (m.next x) := by
  rcases hx with hs | ⟨op, k, r, hs, rfl⟩ | ⟨c, k, r, hs, rfl⟩
  · exact .silent (by simp [observe, hs]) (.refl _)
  · exact .impure r (by simp [observe, hs]; rfl) (.refl _)
  · exact .branch r (by simp [observe, hs]; rfl) (.refl _)

lemma interp_hasOutcome {σ : Type u} {h : ∀ {X : Type u}, σ → Step E N A X → Step F M B (σ × X)}
    (hf : Faithful h) {st : σ} {m : CoFree E N A} {b : B}
    (ho : HasOutcome (interp h st m) (.res b)) :
    ∃ st' m', Reaches m m' ∧ h st' (m'.step m'.initial) = .pure b := by
  generalize hM : interp h st m = X at ho
  generalize hb : (Outcome.res b : Outcome F B) = o at ho
  have hnext : ∀ (st : σ) (m : CoFree E N A), (interp h st m).observe =
      (h st (m.step m.initial)).map fun x => interp h x.1 (m.next x.2) := by
    intro st m
    rw [observe_interp]
    exact Step.map_congr (fun ⟨_, x⟩ => by cases x <;> rfl) _
  induction ho generalizing st m with
  | res hv =>
    subst hM; cases hb
    rw [hnext] at hv
    cases hs : h st (m.step m.initial) with
    | pure => rw [hs] at hv; cases hv; exact ⟨st, m, .refl _, hs⟩
    | silent => rw [hs] at hv; cases hv
    | impure => rw [hs] at hv; cases hv
    | branch => rw [hs] at hv; cases hv
  | terminal => cases hb
  | silent _ hs ih =>
    subst hM; subst hb
    rw [hnext] at hs
    cases hh : h st (m.step m.initial) with
    | silent x =>
      rw [hh] at hs
      injection hs with hs
      obtain ⟨st', m', hr, he⟩ := ih hs rfl
      exact ⟨st', m', reaches_trans (reaches_next ((hf st _).1 x hh)) hr, he⟩
    | pure => rw [hh] at hs; cases hs
    | impure => rw [hh] at hs; cases hs
    | branch => rw [hh] at hs; cases hs
  | branch _ hs ih =>
    subst hM; subst hb
    obtain ⟨br, k, hs, r, rfl⟩ := hs
    rw [hnext] at hs
    cases hh : h st (m.step m.initial) with
    | branch c k' =>
      rw [hh] at hs
      simp only [Step.map] at hs
      injection hs with hc hk
      subst hc; cases hk
      obtain ⟨st', m', hr, he⟩ := ih rfl rfl
      exact ⟨st', m', reaches_trans (reaches_next ((hf st _).2.2 c k' r hh)) hr, he⟩
    | pure => rw [hh] at hs; cases hs
    | silent => rw [hh] at hs; cases hs
    | impure => rw [hh] at hs; cases hs
  | impure _ hs ih =>
    subst hM; subst hb
    obtain ⟨op, k, hs, r, rfl⟩ := hs
    rw [hnext] at hs
    cases hh : h st (m.step m.initial) with
    | impure op' k' =>
      rw [hh] at hs
      simp only [Step.map] at hs
      injection hs with hc hk
      subst hc; cases hk
      obtain ⟨st', m', hr, he⟩ := ih rfl rfl
      exact ⟨st', m', reaches_trans (reaches_next ((hf st _).2.1 op' k' r hh)) hr, he⟩
    | pure => rw [hh] at hs; cases hs
    | silent => rw [hh] at hs; cases hs
    | branch => rw [hh] at hs; cases hs

end Outcome

def BadS (_k : ExecutionModeKind) : EvalE.Op → Prop
  | .inr (.ub (.malformed _)) => True
  | _ => False

lemma memStep_faithful : Faithful (@memStep) := by
  intro X mem s
  refine ⟨fun x hx => ?_, fun op k r hx => ?_, fun c k r hx => ?_⟩ <;>
  · rcases s with a | x' | op' | c'
    · exact nomatch a
    · simp only [memStep] at hx
      first | (cases hx; done) | (cases hx; exact .inl rfl)
    · rcases op' with hop | sop
      · simp only [memStep] at hx
        first | (cases hx; done) | (cases hx; exact .inr (.inl ⟨_, _, _, rfl, rfl⟩))
      · cases sop <;> simp only [memStep] at hx <;> (try split at hx) <;> (try split at hx) <;>
          first | (cases hx; done) | (cases hx; exact .inr (.inl ⟨_, _, _, rfl, rfl⟩))
    · exact nomatch c'

lemma memStep_malformed {X : Type} {mem : MemState} {s : Step EvalE .none Empty X} {r : String}
    (h : memStep mem s = .pure (.malformed r)) : ∃ k, s = .impure (.inr (.ub (.malformed r))) k := by
  rcases s with a | x | op | c
  · exact nomatch a
  · simp [memStep] at h
  · rcases op with hop | sop
    · simp [memStep] at h
    · cases sop <;> simp only [memStep] at h <;> (try split at h) <;> (try split at h) <;>
        (try cases h) <;> exact ⟨_, rfl⟩
  · exact nomatch c

lemma hostStep_faithful {N : NonDeterminism} {A : Type} (self : Address) :
    Faithful (fun {X} h s => @hostStep N A X self h s) := by
  intro X hs s
  refine ⟨fun x hx => ?_, fun op k r hx => ?_, fun c k r hx => ?_⟩ <;>
  · rcases s with a | x' | op' | c'
    · simp only [hostStep] at hx; cases hx
    · simp only [hostStep] at hx
      first | (cases hx; done) | (cases hx; exact .inl rfl)
    · simp only [hostStep] at hx
      split at hx <;> (try split at hx) <;>
        first | (cases hx; done) | (cases hx; exact .inr (.inl ⟨_, _, _, rfl, rfl⟩))
    · simp only [hostStep] at hx
      first | (cases hx; done) | (cases hx; exact .inr (.inr ⟨_, _, _, rfl, rfl⟩))

lemma hostStep_inl {N : NonDeterminism} {A X : Type} {self : Address} {hs : HostState}
    {s : Step HostE N A X} {a : A} (h : hostStep self hs s = .pure (.inl a)) : s = .pure a := by
  rcases s with a' | x | op | c
  · simp only [hostStep] at h; cases h; rfl
  · simp [hostStep] at h
  · simp only [hostStep] at h
    split at h <;> (try split at h) <;> cases h
  · simp [hostStep] at h

lemma interpMem_hasOutcome {sir : SirM Empty} {u : UB} (h : HasOutcome (interpMem sir) (.res u)) :
    ∃ mem, HasOutcome (interp memStep mem sir) (.res u) := by
  have ho : (interpMem sir).observe =
      .branch (.pick (Word.size - CompilerReservedBytes) (by decide)) fun r =>
      (CoFree.pure r).bind fun (start : Fin _) =>
      interp memStep { live := #[], reserved := ⟨start.val, CompilerReservedBytes⟩ } sir := by
    unfold interpMem
    exact (observe_bind _ _).trans (by rw [observe_branch]; rfl)
  cases h with
  | res hv => rw [ho] at hv; cases hv
  | silent _ hs => rw [ho] at hs; cases hs
  | impure _ hs => obtain ⟨_, _, hs, _⟩ := hs; rw [ho] at hs; cases hs
  | branch hm hs =>
    obtain ⟨br, k, hs, r, rfl⟩ := hs
    rw [ho] at hs
    injection hs with hc hk
    subst hc; cases hk
    exact ⟨_, hasOutcome_congr (by rw [observe_bind, observe_pure]; rfl) hm⟩

lemma run_malformed {ctx : Context} {w₀ : World} {r : String}
    (hg : Good (BadS ctx.mode.kind) (fun _ _ => True) (fun _ => True) (runInner ctx))
    (h : HasOutcome (interpHost ctx.env.address w₀ (interpMem (runInner ctx)))
      (.res (.inl (.malformed r)))) : False := by
  obtain ⟨_, M, hr, hM⟩ := interp_hasOutcome (hostStep_faithful _) h
  have hM' := hostStep_inl hM
  obtain ⟨mem, hmem⟩ := interpMem_hasOutcome (hasOutcome_of_reaches hr (.res (by
    simp [observe, hM']; rfl)))
  obtain ⟨_, sir', hr', hs⟩ := interp_hasOutcome memStep_faithful hmem
  obtain ⟨k, hk⟩ := memStep_malformed hs
  have := good_reaches hg hr' _ (sir'.next ∘ k) (by simp [observe, hk]; rfl)
  exact this trivial

abbrev GoodS {α : Type} (k : ExecutionModeKind) (Q : α → Prop) (m : SirM α) : Prop :=
  Good (BadS k) (fun _ _ => True) Q m

variable {k : ExecutionModeKind}

lemma good_host {α : Type} (m : HostM α) :
    Good (fun _ => False) (fun _ _ => True) (fun _ => True) m :=
  ⟨fun _ => True, trivial, fun x _ => by unfold Closed; split <;> simp⟩

lemma good_halt {α : Type} (o : SimplifiedOutcome) (Q : α → Prop) :
    Good (fun _ => False) (fun _ _ => True) Q (Host.halt o : HostM α) :=
  good_bind (good_perform (Q := fun _ => False) (fun h => h) fun r => nomatch r) fun _ h => h.elim

lemma goodS_liftHost {α : Type} (m : HostM α) : GoodS k (fun _ => True) (m.mapOps ⟨Sum.inl, fun _ r => r⟩ .id : SirM α) :=
  good_mapOps _ _ (fun _ h => h) (fun _ _ _ => trivial) (good_host m)

lemma goodS_halt {α : Type} (o : SimplifiedOutcome) (Q : α → Prop) :
    GoodS k Q ((Host.halt o : HostM α).mapOps ⟨Sum.inl, fun _ r => r⟩ .id : SirM α) :=
  good_mapOps _ _ (fun _ h => h) (fun _ _ _ => trivial) (good_halt o Q)

lemma goodS_sirOp (op : SirOp) (hop : ∀ r, op ≠ .ub (.malformed r)) :
    GoodS k (fun _ => True) (perform (E := EvalE) (.inr op) : SirM _) :=
  good_perform (by cases op <;> (try rename_i u; cases u) <;> simp_all [BadS]) fun _ _ => trivial

lemma goodS_read (o n : Word) : GoodS k (fun _ => True) (mem.read o n) :=
  goodS_sirOp (.read o n) (fun _ h => by cases h)

lemma goodS_write (o : Word) (b : ByteArray) : GoodS k (fun _ => True) (mem.write o b) :=
  goodS_sirOp (.write o b) (fun _ h => by cases h)

lemma goodS_copy (c : MemCopy) : GoodS k (fun _ => True) (mem.copy c) :=
  goodS_sirOp (.copy c) (fun _ h => by cases h)

lemma goodS_allocZeroed (n : Word) : GoodS k (fun _ => True) (alloc_zeroed n) :=
  goodS_sirOp (.alloc .zeroed n) (fun _ h => by cases h)

lemma goodS_allocUninit (n : Word) : GoodS k (fun _ => True) (alloc_uninit n) :=
  goodS_sirOp (.alloc .uninitialized n) (fun _ h => by cases h)

lemma goodS_ub {α : Type} (u : UB) (hu : ∀ r, u ≠ .malformed r) (Q : α → Prop) :
    GoodS k Q (ub u : SirM α) :=
  good_bind (good_perform (E := EvalE) (op := .inr (.ub u)) (Q := fun _ => False)
    (by cases u <;> simp_all [BadS]) fun r => nomatch r) fun r => nomatch r

lemma goodS_returndataSize : GoodS k (fun _ => True) returndata.size :=
  good_bind (goodS_liftHost _) fun _ _ => good_pure trivial

lemma goodS_checkStateful (ctx : Context) : GoodS k (fun _ => True) ctx.checkStateful := by
  unfold Context.checkStateful; split
  · exact goodS_halt _ _
  · exact good_pure trivial


section MapM

variable {E : Effect.{u}} {N : NonDeterminism.{u}} {Bad : E.Op → Prop}
  {Ok : (op : E.Op) → E.Resp op → Prop}

lemma good_mapM {α β : Type u} (f : α → CoFree E N β) (xs : Array α)
    (hf : ∀ i (h : i < xs.size), Good Bad Ok (fun _ => True) (f xs[i])) :
    Good Bad Ok (fun ys => ys.size = xs.size) (xs.mapM f) := by
  have aux : ∀ n i (bs : Array β), xs.size - i = n → i ≤ xs.size → bs.size = i →
      Good Bad Ok (fun ys => ys.size = xs.size) (arrayMapM_map% f xs i bs) := by
    intro n
    induction n with
    | zero =>
      intro i bs hn hi hbs
      rw [arrayMapM_map_eq%]
      split
      · omega
      · exact good_pure (by omega)
    | succ n ih =>
      intro i bs hn hi hbs
      rw [arrayMapM_map_eq%]
      split
      · rename_i hlt
        exact good_bind (hf i hlt) fun _ _ => ih (i + 1) _ (by omega) (by omega) (by simp [hbs])
      · omega
  unfold Array.mapM
  exact aux _ 0 _ rfl (by omega) (by simp)

end MapM

lemma varId_compare (a b : VarId) : compare a b = compare a.id b.id := by
  cases a; cases b; simp [compare, Sir.instOrdVarId.ord]

instance : Std.TransCmp (compare : VarId → VarId → Ordering) where
  eq_swap := by
    intro a b; rw [varId_compare, varId_compare]; exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c; rw [varId_compare, varId_compare, varId_compare]; exact Std.TransCmp.isLE_trans

lemma mem_insert_self (t : Vars) (v : VarId) (w : Word) : v ∈ t.insert v w :=
  Std.TreeMap.mem_insert.2 (.inl (by rw [varId_compare]; exact Nat.compare_eq_eq.2 rfl))

lemma mem_insert_of_mem {t : Vars} {a : VarId} (k : VarId) (w : Word) (h : a ∈ t) :
    a ∈ t.insert k w :=
  Std.TreeMap.mem_insert.2 (.inr h)

lemma goodS_lookup {vars : Vars} {v : VarId} (h : v ∈ vars) :
    GoodS k (fun _ => True) (vars.lookup v) := by
  unfold Vars.lookup
  have := Std.TreeMap.mem_iff_isSome_getElem?.1 h
  cases hv : vars[v]? with
  | none => rw [hv] at this; cases this
  | some w => exact good_pure trivial

lemma goodS_lookupAll {vars : Vars} {vs : Array VarId} (h : ∀ v ∈ vs.toList, v ∈ vars) :
    GoodS k (fun ws => ws.size = vs.size) (vars.lookupAll vs) :=
  good_mapM _ _ fun i hi => goodS_lookup (h _ (by simp))

lemma mem_foldl_insert :
    ∀ (l : List (VarId × Word)) (t : Vars) (a : VarId), a ∈ l.map Prod.fst ∨ a ∈ t →
      a ∈ l.foldl (fun t (x : VarId × Word) => t.insert x.1 x.2) t
  | [], _, _, h => by simpa using h
  | (v, w) :: l, t, a, h => by
    refine mem_foldl_insert l _ a ?_
    rcases h with h | h
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr (mem_insert_self _ _ _)
      · exact .inl h
    · exact .inr (mem_insert_of_mem _ _ h)

lemma goodS_assignAll {l₀ : Vars} {vs : Array VarId} {ws : Array Word} (h : vs.size = ws.size) :
    GoodS k (fun l => ∀ a, a ∈ vs.toList ∨ a ∈ l₀ → a ∈ l) (l₀.assignAll vs ws) := by
  unfold Vars.assignAll
  simp only [h, ↓reduceIte]
  refine good_pure fun a ha => ?_
  rw [← Array.foldl_toList]
  refine mem_foldl_insert _ _ a ?_
  rcases ha with ha | ha
  · left
    rw [Array.toList_zip, List.map_fst_zip (by simp [h])]
    exact ha
  · exact .inr ha

lemma goodS_exprResolve {vars : Vars} {e : Expr VarId} (h : ∀ v ∈ e.reads, v ∈ vars) :
    GoodS k (fun e' => ∀ p k', e'.ValidIn p k' ↔ e.ValidIn p k') (e.resolve vars.lookup) := by
  cases e <;> simp only [Expr.resolve] <;>
    repeat (first
      | exact good_pure (fun _ k' => by cases k' <;> exact Iff.rfl)
      | refine good_bind (goodS_lookup (h _ (by simp [Expr.reads]))) fun _ _ => ?_)

lemma goodS_stmtResolve {vars : Vars} {s : Stmt VarId} (h : ∀ v ∈ s.reads, v ∈ vars) :
    GoodS k (fun s' => ∀ p k', s'.ValidIn p k' ↔ s.ValidIn p k') (s.resolve vars.lookup) := by
  cases s <;> simp only [Stmt.resolve] <;>
    repeat (first
      | exact good_pure (fun _ k' => by cases k' <;> exact Iff.rfl)
      | refine good_bind (goodS_lookup (h _ (by simp [Stmt.reads]))) fun _ _ => ?_)

def OpMatch : Operation VarId → Operation Word → Prop
  | .let out e, .let out' e' => out' = out ∧ ∀ p k, e'.ValidIn p k ↔ e.ValidIn p k
  | .icall g ins outs, .icall g' args outs' => g' = g ∧ args.size = ins.size ∧ outs' = outs
  | .stmt s, .stmt s' => ∀ p k, s'.ValidIn p k ↔ s.ValidIn p k
  | _, _ => False

lemma goodS_opResolve {vars : Vars} {op : Operation VarId} (h : ∀ v ∈ op.reads, v ∈ vars) :
    GoodS k (OpMatch op) (op.resolve vars.lookup) := by
  cases op with
  | «let» out e =>
    exact good_bind (goodS_exprResolve h) fun _ he => good_pure ⟨rfl, he⟩
  | icall g ins outs =>
    exact good_bind (goodS_lookupAll h) fun _ hs => good_pure ⟨rfl, hs, rfl⟩
  | stmt s =>
    exact good_bind (goodS_stmtResolve h) fun _ hs => good_pure hs

def CtrlMatch : Control VarId → Control Word → Prop
  | .iret, .iret | .stop, .stop | .invalid, .invalid => True
  | .return .., .return .. | .revert .., .revert .. | .selfdestruct _, .selfdestruct _ => True
  | .continuesTo t, .continuesTo t' => t' = t
  | .branches _ a b, .branches _ a' b' => a' = a ∧ b' = b
  | .switch _ cs fb, .switch _ cs' fb' => cs' = cs ∧ fb' = fb
  | .icallNever g ins, .icallNever g' args => g' = g ∧ args.size = ins.size
  | _, _ => False

lemma goodS_ctrlResolve {vars : Vars} {c : Control VarId} (h : ∀ v ∈ c.reads, v ∈ vars) :
    GoodS k (CtrlMatch c) (c.resolve vars.lookup) := by
  cases c with
  | icallNever g ins =>
    exact good_bind (goodS_lookupAll h) fun _ hs => good_pure ⟨rfl, hs⟩
  | _ =>
    simp only [Control.resolve] <;>
      repeat (first
        | exact good_pure (by simp [CtrlMatch])
        | refine good_bind (goodS_lookup (h _ (by simp [Control.reads]))) fun _ _ => ?_)

lemma good_map {E : Effect.{u}} {N : NonDeterminism.{u}} {Bad : E.Op → Prop}
    {Ok : (op : E.Op) → E.Resp op → Prop} {A B : Type u} {Q₁ : A → Prop} {Q : B → Prop}
    {x : CoFree E N A} {f : A → B} (h : Good Bad Ok Q₁ x) (hf : ∀ a, Q₁ a → Q (f a)) :
    Good Bad Ok Q (f <$> x) :=
  good_bind h fun a ha => good_pure (hf a ha)

syntax "good_auto" : tactic
macro_rules
  | `(tactic| good_auto) => `(tactic| repeat (first
      | exact good_pure trivial
      | exact goodS_read _ _
      | exact goodS_write _ _
      | exact goodS_copy _
      | exact goodS_allocZeroed _
      | exact goodS_allocUninit _
      | exact goodS_returndataSize
      | exact goodS_checkStateful _
      | exact goodS_halt _ _
      | exact goodS_liftHost _
      | exact goodS_ub _ (by intro _ h; cases h) _
      | refine good_forIn_list (fun _ _ => True) _ (fun _ _ _ _ => ?_) (fun _ _ => trivial) _ _ trivial
      | refine good_map (Q₁ := fun _ => True) ?_ fun _ _ => trivial
      | refine good_bind (Q₁ := fun _ => True) ?_ fun _ _ => ?_
      | split))

def ImmsWF (ctx : Context) : Prop :=
  ∀ h : ctx.mode.kind = .call, (h ▸ ctx.immutables).getMain.WF ctx.program

lemma goodS_code {ctx : Context} (hI : ImmsWF ctx) : GoodS k (fun _ => True) ctx.code := by
  obtain ⟨p, l, mode, env, imms⟩ := ctx
  cases mode with
  | creation c => exact good_pure trivial
  | call s cd =>
    cases imms with
    | main m =>
      have hm : m.WF p := hI rfl
      simp only [Context.code, Immutables.getMain, Layout.withSetImmutables, hm, ↓reduceDIte]
      exact good_pure trivial

lemma goodS_execCall (ctx : Context) (ck : CallKind) (g a io il oo ol : Word) :
    GoodS k (fun _ => True) (execCall ctx ck g a io il oo ol) := by
  unfold execCall mem.writeFromSlice
  good_auto

lemma goodS_query (env : Env) (q : Query) : GoodS k (fun _ => True) (q.eval env) := by
  cases q <;> simp only [Query.eval] <;> good_auto

lemma goodS_log (ctx : Context) (o n : Word) (ts : Array Word) :
    GoodS k (fun _ => True) (log ctx o n ts) := by
  unfold log; good_auto

lemma goodS_getDataOffset {ctx : Context} {d : DataId}
    (he : (Expr.dataOffset d : Expr Word).ValidIn ctx.program ctx.mode.kind) :
    GoodS ctx.mode.kind (fun _ => True) (ctx.getDataOffset d) := by
  obtain ⟨p, l, mode, env, imms⟩ := ctx
  cases mode with
  | creation c =>
    simp only [Context.getDataOffset, ExecutionMode.kind] at he ⊢
    split
    · exact good_bind (Q₁ := fun _ => True) (good_pure trivial) fun _ _ => good_pure trivial
    · contradiction
  | call s cd =>
    simp only [Context.getDataOffset, ExecutionMode.kind] at he ⊢
    obtain ⟨hv, hm⟩ := he
    split
    · refine good_bind (Q₁ := fun x => x = ⟨d.id, hv⟩) (good_pure rfl) fun _ hx => ?_
      subst hx
      split
      · exact good_pure trivial
      · contradiction
    · contradiction

lemma goodS_getImmutable {ctx : Context} {i : ImmutableId}
    (he : (Expr.getImmutable i : Expr Word).ValidIn ctx.program ctx.mode.kind) (hI : ImmsWF ctx) :
    GoodS ctx.mode.kind (fun _ => True) (ctx.getImmutable i) := by
  obtain ⟨p, l, mode, env, imms⟩ := ctx
  cases mode with
  | creation c => simp [Expr.ValidIn, ExecutionMode.kind] at he
  | call s cd =>
    cases imms with
    | main m =>
      obtain ⟨hsz, hvals⟩ := (hI rfl : m.WF p)
      simp only [Immutables.getMain] at hsz hvals
      simp only [Expr.ValidIn, ExecutionMode.kind, Program.ValidImmutableId] at he
      simp only [Context.getImmutable, ExecutionMode.kind]
      refine good_bind (Q₁ := fun x => x = m.slots) (good_pure rfl) fun _ hx => ?_
      subst hx
      have h1 : p[i]? = some p.immutables[i.id] := by
        simp [getElem?, he]
      have h2 : m.slots[i.id]? = some m.slots[i.id] := by
        simp [hsz, he]
      simp only [h1, h2]
      have h3 := hvals ⟨i.id, he⟩
      simp only [Fin.getElem_fin] at h3
      simp only [h3, ↓reduceIte]
      exact good_pure trivial

lemma goodS_exprEval {ctx : Context} {e : Expr Word} (he : e.ValidIn ctx.program ctx.mode.kind)
    (hI : ImmsWF ctx) : GoodS ctx.mode.kind (fun _ => True) (e.eval ctx) := by
  cases e <;> simp only [Expr.eval]
  case dataOffset => exact goodS_getDataOffset he
  case getImmutable => exact goodS_getImmutable he hI
  case mainStartOffset | initEndOffset =>
    have hk : ctx.mode.kind = .creation := by
      revert he; cases ctx.mode.kind <;> simp [Expr.ValidIn]
    simp only [hk, ↓reduceIte]
    good_auto
  case extcodehash a | extcodesize a =>
    by_cases hs : Address.ofWord a = ctx.env.address <;> simp only [hs, ↓reduceIte]
    · refine good_bind (Q₁ := fun _ => True) ?_ fun _ _ => good_pure trivial
      unfold Context.deployedCode; split
      · exact good_pure trivial
      · exact goodS_code hI
    · good_auto
  all_goals first
    | exact goodS_execCall _ _ _ _ _ _ _ _
    | exact goodS_query _ _
    | skip
  all_goals try good_auto
  all_goals exact goodS_code hI

lemma goodS_stmtExec {ctx : Context} {s : Stmt Word} (hs : s.ValidIn ctx.program ctx.mode.kind)
    (hI : ImmsWF ctx) : GoodS ctx.mode.kind (fun _ => True) (s.exec ctx) := by
  cases s <;> simp only [Stmt.exec]
  case setImmutable id ptr v =>
    have hk : ctx.mode.kind = .creation := by
      revert hs; cases ctx.mode.kind <;> simp [Stmt.ValidIn]
    have hv : ctx.program.ValidImmutableId id := by
      revert hs; rw [hk]; simp [Stmt.ValidIn]
    simp only [hk, ↓reduceIte, hv, ↓reduceDIte]
    refine good_bind (Q₁ := fun _ => True) (good_pure trivial) fun _ _ => ?_
    good_auto
  case codecopy =>
    exact good_bind (goodS_code hI) fun _ _ => by unfold mem.writeFromSlice; good_auto
  all_goals first
    | exact goodS_log _ _ _ _
    | (unfold mem.writeFromSlice; good_auto)
    | good_auto

lemma goodS_evalSwitch (cond : Word) (cases : Array (Word × BlockId)) (fallback : Option BlockId) :
    GoodS k (fun d => d ∈ cases.toList.map (·.2) ∨ fallback = some d)
      (evalSwitch cond cases fallback) := by
  unfold evalSwitch
  refine good_bind (Q₁ := fun b => b.1 = none ∨ ∃ d, b.1 = some d ∧ d ∈ cases.toList.map (·.2))
    (good_forIn_array (fun _ b => b.1 = none) cases _ (fun i hi b _ => ?_) (fun _ h => .inl h) rfl)
    fun b hb => ?_
  · rcases hc : cases[i] with ⟨value, dst⟩
    simp only
    split
    · refine good_pure (.inr ⟨dst, rfl, ?_⟩)
      exact List.mem_map.2 ⟨(value, dst), by rw [← hc]; simp, rfl⟩
    · exact good_pure rfl
  · rcases hb with hb | ⟨d, hb, hd⟩
    · simp only [hb]
      split
      · exact good_pure (.inr rfl)
      · exact goodS_ub _ (by intro _ h; cases h) _
    · simp only [hb]
      exact good_pure (.inl hd)

abbrev RecE := Effect.Rec CallI CallO EvalE

lemma goodR_lift {Pre : CallI → Prop} {Post : CallI → CallO → Prop} {α : Type} {Q : α → Prop}
    {m : SirM α} (h : GoodS k Q m) :
    Good (RecBad Pre (BadS k)) (RecOk Post fun _ _ => True) Q
      (m.mapOps ⟨Sum.inr, fun _ r => r⟩ .id : CoFree RecE .none α) :=
  good_mapOps _ _ (fun _ h => h) (fun _ _ _ => trivial) h

lemma definedBefore_succ (b : Block) {i : Nat} (hi : i < b.ops.size) :
    b.definedBefore (i + 1) = b.definedBefore i ++ b.ops[i].defs := by
  simp [Block.definedBefore, List.take_add_one, hi]

lemma definedBefore_size (b : Block) : b.definedBefore b.ops.size = b.defs := by
  simp [Block.definedBefore, Block.defs,
    List.take_of_length_le (by simp : b.ops.toList.length ≤ b.ops.size)]

lemma definedBeforeUse_mono (b : Block) (pre pre' : List VarId) (hsub : pre ⊆ pre')
    (h : b.DefinedBeforeUse pre) : b.DefinedBeforeUse pre' :=
  have hs : ∀ l : List VarId, pre ++ l ⊆ pre' ++ l := fun l x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ (hsub hx)
    · exact List.mem_append_right _ hx
  ⟨fun i hi v hv => hs _ (h.1 i hi v hv), fun v hv => hs _ (h.2 v hv)⟩

lemma mem_functions {p : Program} {f : FunctionId} {fn : Function} (h : p[f]? = some fn) :
    fn ∈ p.functions :=
  Array.mem_of_getElem? h

lemma mem_blocks {fn : Function} {b : BlockId} {blk : Block} (h : fn[b]? = some blk) :
    blk ∈ fn.blocks :=
  Array.mem_of_getElem? h

section EvalFn

variable (ctx : Context) (root : FunctionId)

def Pre (x : CallI) : Prop :=
  ∃ fn, ctx.program[x.1]? = some fn ∧ ctx.program.Reachable root x.1 ∧
    ∃ entry, fn[fn.entry]? = some entry ∧ entry.inputs.size = x.2.size

def Post (x : CallI) (outs : CallO) : Prop :=
  ∃ fn, ctx.program[x.1]? = some fn ∧ fn.returns = .values outs.size

lemma good_evalFn {x : CallI} (hwf : ctx.program.WF)
    (hroot : ctx.program.ValidFrom ctx.mode.kind root) (hI : ImmsWF ctx) (hx : Pre ctx root x) :
    GoodS ctx.mode.kind (Post ctx x) (evalFn ctx x) := by
  unfold evalFn
  refine good_fix (Pre := Pre ctx root) _ (fun x hx => ?_) hx
  obtain ⟨fid, args⟩ := x
  obtain ⟨fn, hfn, hreach, entry, hentry, hargs⟩ := hx
  have hfwf := hwf.functions fn (mem_functions hfn)
  simp only [hfn]
  refine good_bind (Q₁ := fun s => ∃ r, s.1 = some r ∧ Post ctx (fid, args) r)
    (good_loop (fun s => ∃ blk, fn[s.2.2.1]? = some blk ∧ s.2.1.size = blk.inputs.size ∧
        ∃ prev, fn.PathTo prev s.2.2.1 ∧ ∀ x ∈ prev.flatMap Block.defs, x ∈ s.2.2.2) _
      (fun st hst => ?_) ⟨entry, hentry, hargs.symm, [], .entry, by simp⟩) fun st hst => ?_
  case refine_2 =>
    obtain ⟨r, hr, hp⟩ := hst
    simp only [hr]
    exact good_pure hp
  obtain ⟨blk, hblk, hsz, prev, hpath, hprev⟩ := hst
  have hmem := mem_blocks hblk
  have hdbu := hfwf.definedBeforeUse prev _ blk hpath hblk
  simp only [hblk]
  refine good_bind (goodR_lift (goodS_assignAll hsz.symm)) fun vars hvars => ?_
  refine good_bind
    (Q₁ := fun v => ∀ x ∈ prev.flatMap Block.defs ++ blk.definedBefore blk.ops.size, x ∈ v)
    (good_forIn_array (fun i v => ∀ x ∈ prev.flatMap Block.defs ++ blk.definedBefore i, x ∈ v)
      blk.ops _ (fun i hi v hv => ?_) (fun _ h => h) ?_) fun vars' hvars' => ?_
  rotate_left
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hvars x (.inr (hprev x hx))
    · exact hvars x (.inl (by simpa [Block.definedBefore] using hx))
  · have hcalls := (hwf.validCalls fn (mem_functions hfn) blk hmem).2
    have hdef : ∀ x ∈ blk.outputs.toList, x ∈ vars' := fun x hx =>
      hvars' x (hdbu.2 x (List.mem_append_right _ hx))
    have htgt : ∀ t ∈ blk.control.targets, ∀ inputs : Array Word, inputs.size = blk.outputs.size →
        ∃ tb, fn[t]? = some tb ∧ inputs.size = tb.inputs.size ∧
          ∃ prev', fn.PathTo prev' t ∧ ∀ x ∈ prev'.flatMap Block.defs, x ∈ vars' := by
      intro t ht inputs hin
      obtain ⟨tb, htb, hs⟩ := hfwf.validTargets blk hmem t ht
      refine ⟨tb, htb, hin.trans hs.symm, prev ++ [blk], .step hpath hblk ht, fun x hx => ?_⟩
      rw [List.flatMap_append, List.flatMap_singleton, ← definedBefore_size] at hx
      exact hvars' x hx
    refine good_bind (goodR_lift (goodS_ctrlResolve fun x hx =>
      hvars' x (hdbu.2 x (List.mem_append_left _ hx)))) fun c' hc => ?_
    rcases hcb : blk.control with _ | t | ⟨_, nz, z⟩ | ⟨_, cs, fb⟩ | _ | _ | _ | _ | _ | ⟨g, ins⟩ <;>
      rw [hcb] at hc htgt hcalls <;> cases c' <;> simp only [CtrlMatch] at hc <;>
      (try contradiction) <;> simp only
    · rw [hfwf.iretArity blk hmem hcb]
      refine good_bind (goodR_lift (goodS_lookupAll hdef)) fun outs houts => ?_
      simp only [houts, ↓reduceIte]
      exact good_pure ⟨outs, rfl, fn, hfn, by rw [hfwf.iretArity blk hmem hcb, houts]⟩
    · subst hc
      exact good_bind (Q₁ := fun x => x ∈ blk.control.targets)
        (good_pure (by simp [hcb, Control.targets])) fun _ h =>
        good_bind (goodR_lift (goodS_lookupAll hdef)) fun _ hin => good_pure (htgt _ (by rw [← hcb]; exact h) _ hin)
    · obtain ⟨rfl, rfl⟩ := hc
      refine good_bind (Q₁ := fun x => x ∈ blk.control.targets)
        (good_pure (by rw [hcb]; split <;> simp [Control.targets])) fun _ h =>
        good_bind (goodR_lift (goodS_lookupAll hdef)) fun _ hin => good_pure (htgt _ (by rw [← hcb]; exact h) _ hin)
    · obtain ⟨rfl, rfl⟩ := hc
      refine good_bind (goodR_lift (goodS_evalSwitch _ _ _)) fun _ h =>
        good_bind (goodR_lift (goodS_lookupAll hdef)) fun _ hin => good_pure (htgt _ ?_ _ hin)
      simp only [Control.targets, List.mem_append]
      rcases h with h | h
      · exact .inl h
      · exact .inr (by simp [h])
    · exact good_bind (goodR_lift (goodS_halt _ (fun _ => False))) fun _ h => h.elim
    · exact good_bind (goodR_lift (goodS_read _ _)) fun _ _ =>
        good_bind (goodR_lift (goodS_halt _ (fun _ => False))) fun _ h => h.elim
    · exact good_bind (goodR_lift (goodS_read _ _)) fun _ _ =>
        good_bind (goodR_lift (goodS_halt _ (fun _ => False))) fun _ h => h.elim
    · exact good_bind (goodR_lift (goodS_halt _ (fun _ => False))) fun _ h => h.elim
    · exact good_bind (goodR_lift (goodS_checkStateful _)) fun _ _ =>
        good_bind (goodR_lift (goodS_halt _ (fun _ => False))) fun _ h => h.elim
    · rename_i g' args'
      obtain ⟨rfl, hsz'⟩ := hc
      obtain ⟨f, hf, hnever, e, he, hes⟩ := hcalls
      have hpre : Pre ctx root (g', args') :=
        ⟨f, hf, .call hreach ⟨_, hfn, _, _, _, hpath, hblk, .inr (by rw [hcb]; rfl)⟩, e, he, by rw [hsz']; exact hes⟩
      refine good_bind (good_perform (E := RecE) (op := .inl (g', args'))
        (Q := Post ctx (g', args')) (fun h => h hpre) fun _ hr => hr) fun _ hr => ?_
      obtain ⟨f', hf', hr'⟩ := hr
      rw [hf] at hf'
      cases hf'
      rw [hnever] at hr'
      cases hr'
  · have hop_mem : blk.ops[i] ∈ blk.ops := Array.getElem_mem hi
    have hvalid := hroot fid fn hreach hfn prev _ blk hpath hblk _ hop_mem
    have hcall := (hwf.validCalls fn (mem_functions hfn) blk hmem).1 _ hop_mem
    have hreach' : ∀ g, blk.ops[i].callee? = some g → ctx.program.Reachable root g :=
      fun g hg => .call hreach ⟨_, hfn, _, _, _, hpath, hblk, .inl ⟨_, hop_mem, hg⟩⟩
    refine good_bind (goodR_lift (goodS_opResolve fun x hx => hv x (hdbu.1 i hi x hx)))
      fun op' hop => ?_
    simp only [definedBefore_succ blk hi, ← List.append_assoc]
    generalize blk.ops[i] = op at hop hvalid hcall hreach' ⊢
    cases op <;> cases op' <;> simp only [OpMatch] at hop <;> (try contradiction) <;> simp only
    · obtain ⟨rfl, he⟩ := hop
      refine good_bind (goodR_lift (goodS_exprEval ((he _ _).2 hvalid) hI)) fun w _ =>
        good_pure fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · exact mem_insert_of_mem _ _ (hv x hx)
      · simp only [Operation.defs, List.mem_singleton] at hx
        subst hx
        exact mem_insert_self _ _ _
    · rename_i g ins outs g' args' outs'
      obtain ⟨rfl, hsz', rfl⟩ := hop
      obtain ⟨f, hf, hret, e, he, hes⟩ := hcall
      have hpre : Pre ctx root (g', args') :=
        ⟨f, hf, hreach' g' rfl, e, he, by rw [hsz']; exact hes⟩
      refine good_bind (good_perform (E := RecE) (op := .inl (g', args'))
        (Q := Post ctx (g', args')) (fun h => h hpre) fun _ hr => hr) fun results hr => ?_
      obtain ⟨f', hf', hr'⟩ := hr
      rw [hf] at hf'
      cases hf'
      rw [hret] at hr'
      injection hr' with hr'
      refine good_bind (goodR_lift (goodS_assignAll hr')) fun v' hv' => good_pure fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · exact hv' x (.inr (hv x hx))
      · exact hv' x (.inl hx)
    · refine good_bind (goodR_lift (goodS_stmtExec ((hop _ _).2 hvalid) hI)) fun _ _ =>
        good_pure fun x hx => ?_
      simp only [Operation.defs, List.append_nil] at hx
      exact hv x hx

end EvalFn

lemma good_entry {ctx : Context} {root : FunctionId} (hwf : ctx.program.WF)
    (hI : ImmsWF ctx) (hentry : ctx.program.Callee root 0 .never)
    (hvalid : ctx.program.ValidFrom ctx.mode.kind root) :
    GoodS ctx.mode.kind (fun _ => False) (evalFn ctx (root, #[])) := by
  obtain ⟨fn, hfn, hnever, entry, hentry, hin⟩ := hentry
  refine good_mono (fun _ ⟨f, hf, hr⟩ => ?_)
    (good_evalFn ctx root hwf hvalid hI ⟨fn, hfn, .root, entry, hentry, hin⟩)
  rw [hfn] at hf
  cases hf
  rw [hnever] at hr
  cases hr

lemma good_runInner {ctx : Context} (hwf : ctx.program.WF) (hI : ImmsWF ctx) :
    GoodS ctx.mode.kind (fun _ => True) (runInner ctx) := by
  unfold runInner
  dsimp only
  refine good_bind (Q₁ := fun _ => False) ?_ fun _ h => h.elim
  split
  · rename_i hk
    exact good_entry hwf hI hwf.initEntry (hk ▸ hwf.initOps)
  · rename_i hk
    exact good_entry hwf hI hwf.mainEntry (hk ▸ hwf.mainOps)

lemma hasOutcome_pure {E : Effect.{u}} {N : NonDeterminism.{u}} {A : Type u} {a b : A}
    (h : HasOutcome (CoFree.pure a : CoFree E N A) (.res b)) : a = b := by
  cases h with
  | res h => rw [observe_pure] at h; cases h; rfl
  | silent _ h => rw [observe_pure] at h; cases h
  | branch _ h => obtain ⟨_, _, h, _⟩ := h; rw [observe_pure] at h; cases h
  | impure _ h => obtain ⟨_, _, h, _⟩ := h; rw [observe_pure] at h; cases h

lemma runMain_not_malformed (p : Program) (l : Layout p) (imms : MainImmutables) (static : Bool)
    (calldata : BytesX32) (env : Env) (w₀ : World) (hwf : p.WF) (himms : imms.WF p) :
    ¬∃ r, HasResOutcome (p.runMain l imms static calldata env w₀) (.inl (.malformed r)) := by
  rintro ⟨_, h⟩
  exact run_malformed (ctx := ⟨p, l, .call static calldata, env, .main imms⟩)
    (good_runInner hwf fun _ => himms) h

lemma runInit_not_malformed (p : Program) (l : Layout p) (ctorArgs : ByteArray) (env : Env)
    (w₀ : World) (hwf : p.WF) :
    ¬∃ r, HasResOutcome (p.runInit l ctorArgs env w₀) (.inl (.malformed r)) := by
  rintro ⟨_, h⟩
  obtain ⟨a, ha, hpure⟩ := hasOutcome_bind h
  have hfa := hasOutcome_pure hpure
  rcases a with u | o
  · cases hfa
    exact run_malformed (ctx := ⟨p, l, .creation ctorArgs, env, .init⟩)
      (good_runInner hwf nofun) ha
  · rcases o with ⟨d, s⟩ | _ | _ | _ <;> simp only at hfa <;> (try cases hfa)
    split at hfa <;> cases hfa

lemma runInit_ret_wf (p : Program) (l : Layout p) (ctorArgs : ByteArray) (env : Env) (w₀ : World)
    (imms : MainImmutables) (store : Store)
    (h : HasResOutcome (p.runInit l ctorArgs env w₀) (.inr (.ret imms store))) : imms.WF p := by
  obtain ⟨a, _, hpure⟩ := hasOutcome_bind h
  have hfa := hasOutcome_pure hpure
  rcases a with u | o
  · cases hfa
  · rcases o with ⟨d, s⟩ | _ | _ | _ <;> simp only at hfa <;> (try cases hfa)
    split at hfa
    · rename_i m hm
      cases hfa
      exact l.toMainImmutables_wf _ _ hm
    · cases hfa

lemma deploy_main_not_malformed (p : Program) (l : Layout p) (ctorArgs : ByteArray) (env : Env)
    (w₀ : World) (imms : MainImmutables) (store : Store) (static : Bool) (calldata : BytesX32)
    (env' : Env) (w₁ : World) (reason : String) (hwf : p.WF)
    (h : HasResOutcome (p.runInit l ctorArgs env w₀) (.inr (.ret imms store))) :
    ¬HasResOutcome (p.runMain l imms static calldata env' w₁) (.inl (.malformed reason)) :=
  fun hm => runMain_not_malformed p l imms static calldata env' w₁ hwf
    (runInit_ret_wf p l ctorArgs env w₀ imms store h) ⟨reason, hm⟩

end Sir.Proofs
