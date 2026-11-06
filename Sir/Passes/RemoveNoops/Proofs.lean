import Sir.Passes.RemoveNoops
import Sir.Passes.DeadCode.Proofs

namespace Sir.Proofs.RemoveNoops

open Host CoFree
open Sir.Proofs.DeadCode (RecE CallRel bisim_interpMem bisim_interpHost bisim_map)

section Lookup

lemma program_getElem? (p : Program) (f : FunctionId) :
    p.removeNoops[f]? = p[f]?.map Function.removeNoops :=
  Array.getElem?_map ..

lemma function_getElem? (fn : Function) (b : BlockId) :
    fn.removeNoops[b]? = fn[b]?.map Block.removeNoops :=
  Array.getElem?_map ..

end Lookup

section EvalFn

lemma observe_bind_of_pure {E : Effect} {N : NonDeterminism} {A B : Type} {m : CoFree E N A} {a : A}
    (g : A → CoFree E N B) (h : m.observe = .pure a) : (m >>= g).observe = (g a).observe := by
  show (m.bind g).observe = _
  rw [observe_bind, h]
  rfl

lemma observe_mapOps_of_pure {E F : Effect} {N M : NonDeterminism} {A : Type} {m : CoFree E N A}
    {a : A} (e : Effect.Map E F) (nd : NonDeterminism.Map N M) (h : m.observe = .pure a) :
    (m.mapOps e nd).observe = .pure a := by
  rw [observe_mapOps, h]

lemma forInRel_refl {β : Type} (b : ForInStep β) : ForInRel Eq b b := by cases b <;> rfl

lemma loopRel_refl {β : Type} (b : ForInStep β) : LoopRel Eq Eq b b := by cases b <;> rfl

lemma bisim_self {α : Type} {R : α → α → Prop} (hR : ∀ a, R a a) (m : CoFree RecE .none α) :
    Bisim (CallRel Eq) R m m := by
  refine ⟨Eq, rfl, fun x y hxy => ?_⟩
  subst hxy
  cases x.observe with
  | pure a => exact hR a
  | silent m => exact rfl
  | impure o k =>
    cases o with
    | inl i => exact ⟨rfl, fun r₁ r₂ hr => by cases hr; rfl⟩
    | inr o => exact ⟨rfl, fun r₁ r₂ hr => by cases hr; rfl⟩
  | branch c k => exact ⟨rfl, fun r₁ r₂ hr => by cases hr; rfl⟩

variable {ctx ctx' : Context}

lemma bisim_evalFn (hp : ctx'.program = ctx.program.removeNoops)
    (hexpr : ∀ e, Expr.eval ctx' e = Expr.eval ctx e) (hstmt : ∀ s, Stmt.exec ctx' s = Stmt.exec ctx s)
    (hcs : ctx'.checkStateful = ctx.checkStateful) (i : CallI) :
    Bisim (OpRel.eq EvalE) Eq (evalFn ctx i) (evalFn ctx' i) := by
  unfold evalFn
  refine Bisim.fix (RI := Eq) (fun x₁ x₂ hx => ?_) rfl
  subst hx
  obtain ⟨f, a⟩ := x₁
  have hfn' : ctx'.program[f]? = ctx.program[f]?.map Function.removeNoops := by
    rw [hp]; exact program_getElem? _ _
  dsimp only
  rw [hfn']
  cases ctx.program[f]? with
  | none => exact bisim_self (fun _ => rfl) _
  | some fn =>
    dsimp only
    refine Bisim.bind (Bisim.loop Eq (Ret := Eq) (fun b₁ b₂ hb => ?_) rfl)
      fun _ _ h => h ▸ bisim_self (fun _ => rfl) _
    subst hb
    obtain ⟨o, inp, bi, vars⟩ := b₁
    dsimp only
    rw [function_getElem?]
    cases fn[bi]? with
    | none => exact bisim_self loopRel_refl _
    | some blk =>
      dsimp only
      refine Bisim.bind (bisim_self (fun _ => rfl) _) ?_
      rintro vars _ rfl
      refine Bisim.bind (Bisim.forIn_array_filter Eq (fun op => !op.isNoop) blk.ops
        (fun op _ _ v₁ v₂ hv => ?_) (fun op _ hk v => ?_) rfl) ?_
      · subst hv
        refine Bisim.bind (bisim_self (fun _ => rfl) _) ?_
        rintro o _ rfl
        cases o with
        | «let» out e => dsimp only; rw [hexpr]; exact bisim_self forInRel_refl _
        | stmt st => dsimp only; rw [hstmt]; exact bisim_self forInRel_refl _
        | icall g args outs => exact bisim_self forInRel_refl _
      · cases op with
        | stmt s =>
          cases s <;> simp only [Operation.isNoop, Bool.not_false, Bool.true_eq_false] at hk
          refine (observe_bind_of_pure (a := Operation.stmt Stmt.noop) _ ?_).trans ?_
          · exact observe_mapOps_of_pure _ _
              ((observe_bind_of_pure (a := Stmt.noop) _ (observe_pure _)).trans (observe_pure _))
          · refine (observe_bind_of_pure (a := ()) _ ?_).trans (observe_pure _)
            exact observe_mapOps_of_pure _ _ (observe_pure _)
        | _ => simp [Operation.isNoop] at hk
      rintro vars _ rfl
      rw [hcs]
      exact bisim_self loopRel_refl _

lemma bisim_runInner (hp : ctx'.program = ctx.program.removeNoops)
    (hexpr : ∀ e, Expr.eval ctx' e = Expr.eval ctx e) (hstmt : ∀ s, Stmt.exec ctx' s = Stmt.exec ctx s)
    (hcs : ctx'.checkStateful = ctx.checkStateful) (hk : ctx'.mode.kind = ctx.mode.kind) :
    Bisim (OpRel.eq EvalE) Eq (runInner ctx) (runInner ctx') := by
  unfold runInner
  dsimp only
  rw [hk, hp]
  cases ctx.mode.kind <;> dsimp only <;>
    exact Bisim.bind (bisim_evalFn hp hexpr hstmt hcs _) fun _ _ _ => Bisim.refl (fun _ => rfl) _

end EvalFn

section Run

def layoutBack {p : Program} (l : Layout p.removeNoops) : Layout p :=
  ⟨l.init, l.init_u32, l.main, l.main_u32, l.mainStartOffset, l.initDataOffsets, l.mainDataOffsets,
   l.immutableOffsets, l.atLeastOne_immOffsets, l.no_imm_imm_overlap, l.no_imm_data_overlap⟩

def layoutFwd {p : Program} (l : Layout p) : Layout p.removeNoops :=
  ⟨l.init, l.init_u32, l.main, l.main_u32, l.mainStartOffset, l.initDataOffsets, l.mainDataOffsets,
   l.immutableOffsets, l.atLeastOne_immOffsets, l.no_imm_imm_overlap, l.no_imm_data_overlap⟩

variable (p : Program) (l : Layout p.removeNoops)

lemma bisim_runInit (c : ByteArray) (e : Env) (w₀ : World) :
    Bisim (OpRel.eq WorldE) Eq (p.runInit (layoutBack l) c e w₀) (p.removeNoops.runInit l c e w₀) := by
  unfold Program.runInit Program.run
  refine bisim_map (bisim_interpHost (bisim_interpMem (bisim_runInner ?_ ?_ ?_ ?_ ?_)) _ _) fun o => ?_
  · rfl
  · intro ex; cases ex <;> rfl
  · intro st; cases st <;> rfl
  · rfl
  · rfl
  · rcases o with _ | (_ | _ | _ | _) <;> rfl

lemma bisim_runMain (imms : MainImmutables) (static : Bool) (cd : BytesX32) (e : Env) (w₀ : World) :
    Bisim (OpRel.eq WorldE) Eq (p.runMain (layoutBack l) imms static cd e w₀)
      (p.removeNoops.runMain l imms static cd e w₀) := by
  refine bisim_interpHost (bisim_interpMem (bisim_runInner ?_ ?_ ?_ ?_ ?_)) _ _
  · rfl
  · intro ex; cases ex <;> rfl
  · intro st; cases st <;> rfl
  · rfl
  · rfl

end Run

section Semantics

variable {p : Program}

lemma removeNoops_equiv (hs : Safe p) : Equiv p p.removeNoops := by
  obtain ⟨⟨⟨l⟩, _, H⟩, _⟩ := hs
  refine ⟨⟨l⟩, ⟨layoutFwd l⟩, fun l₁ l₂ e c w₀ hu => ?_⟩
  refine CoFree.Same.mono (fun a b hab => ?_)
    (Same.bisim (H l₁ (layoutBack l₂) e c w₀ hu) (bisim_runInit p l₂ c e w₀))
  rcases a with _ | ⟨m₁, s₁⟩ | _ | _ | _ <;> rcases b with _ | ⟨m₂, s₂⟩ | _ | _ | _ <;>
    simp only [DefinedAnd, DeployOutcomeEquiv] at hab ⊢ <;> try exact hab
  exact ⟨hab.1, fun static cd e' w =>
    Same.bisim (hab.2 static cd e' w) (bisim_runMain p l₂ m₂ static cd e' w)⟩

lemma removeNoops_safe (hs : Safe p) : Safe p.removeNoops := by
  refine ⟨(removeNoops_equiv hs).symm.refl_left, fun l e c w₀ hu => ?_⟩
  obtain ⟨hdet, hret⟩ := hs.2 (layoutBack l) e c w₀ hu
  refine ⟨Deterministic.bisim hdet (bisim_runInit p l c e w₀), fun imms w' ho => ?_⟩
  obtain ⟨hwf, hms⟩ := hret imms w' (HasOutcome.bisim ho (Bisim.symm (bisim_runInit p l c e w₀)))
  exact ⟨hwf, fun e' static cd w =>
    Deterministic.bisim (hms e' static cd w) (bisim_runMain p l imms static cd e' w)⟩

end Semantics

section WF

variable {p : Program}

lemma eq_of_isNoop {op : Operation VarId} (h : op.isNoop = true) : op = .stmt .noop := by
  cases op with
  | stmt s => cases s <;> first | rfl | simp [Operation.isNoop] at h
  | _ => simp [Operation.isNoop] at h

lemma flatMap_defs_filter :
    ∀ (l : List (Operation VarId)),
      (l.filter fun op => !op.isNoop).flatMap Operation.defs = l.flatMap Operation.defs
  | [] => rfl
  | op :: l => by
    rw [List.filter_cons, List.flatMap_cons]
    cases h : op.isNoop
    · simp only [Bool.not_false, ↓reduceIte, List.flatMap_cons, flatMap_defs_filter l]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, flatMap_defs_filter l]
      rw [eq_of_isNoop h]
      rfl

lemma ops_toList (b : Block) :
    b.removeNoops.ops.toList = b.ops.toList.filter fun op => !op.isNoop :=
  Array.toList_filter ..

lemma block_inputs (b : Block) : b.removeNoops.inputs = b.inputs := rfl

lemma block_defs (b : Block) : b.removeNoops.defs = b.defs := by
  unfold Block.defs
  rw [ops_toList, flatMap_defs_filter]
  rfl

lemma function_defs (fn : Function) : fn.removeNoops.defs = fn.defs := by
  unfold Function.defs
  simp only [Function.removeNoops, Array.toList_map, List.flatMap_map, block_defs]

def OpsOk : List VarId → List (Operation VarId) → Prop
  | _, [] => True
  | pre, op :: l => (∀ v ∈ op.reads, v ∈ pre) ∧ OpsOk (pre ++ op.defs) l

lemma opsOk_iff : ∀ (l : List (Operation VarId)) (pre : List VarId),
    OpsOk pre l ↔ ∀ i (h : i < l.length), ∀ v ∈ l[i].reads, v ∈ pre ++ (l.take i).flatMap Operation.defs
  | [], _ => by simp [OpsOk]
  | op :: l, pre => by
    rw [OpsOk, opsOk_iff l]
    constructor
    · rintro ⟨h₀, h⟩ i hi v hv
      cases i with
      | zero => simpa using h₀ v hv
      | succ i =>
        have := h i (by simpa using hi) v hv
        simpa [List.flatMap_cons, List.append_assoc] using this
    · intro h
      refine ⟨fun v hv => by simpa using h 0 (by simp) v hv, fun i hi v hv => ?_⟩
      have := h (i + 1) (by simpa using hi) v hv
      simpa [List.flatMap_cons, List.append_assoc] using this

lemma opsOk_filter : ∀ (l : List (Operation VarId)) (pre : List VarId),
    OpsOk pre l → OpsOk pre (l.filter fun op => !op.isNoop)
  | [], _, h => h
  | op :: l, pre, ⟨h₀, h⟩ => by
    rw [List.filter_cons]
    cases hn : op.isNoop
    · exact ⟨h₀, opsOk_filter l _ h⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [eq_of_isNoop hn] at h
      exact opsOk_filter l pre (by simpa [Operation.defs] using h)

lemma definedBeforeUse {b : Block} {pre : List VarId} (h : b.DefinedBeforeUse pre) :
    b.removeNoops.DefinedBeforeUse pre := by
  obtain ⟨hops, hctrl⟩ := h
  have hok : OpsOk (pre ++ b.inputs.toList) b.ops.toList := by
    rw [opsOk_iff]
    intro i hi v hv
    have := hops i (by simpa using hi) v (by simpa using hv)
    simpa [Block.definedBefore, List.append_assoc] using this
  have hok' := opsOk_filter _ _ hok
  rw [← ops_toList, opsOk_iff] at hok'
  refine ⟨fun i hi v hv => ?_, fun v hv => ?_⟩
  · have := hok' i (by simpa using hi) v (by simpa using hv)
    simpa [Block.definedBefore, block_inputs, List.append_assoc] using this
  · have := hctrl v hv
    simp only [Block.definedBefore, block_inputs] at this ⊢
    rw [List.take_of_length_le (by simp)] at this ⊢
    rw [ops_toList, flatMap_defs_filter]
    exact this

lemma pathTo_back {fn : Function} {prev' : List Block} {b : BlockId}
    (h : fn.removeNoops.PathTo prev' b) :
    ∃ prev, fn.PathTo prev b ∧ prev' = prev.map Block.removeNoops := by
  induction h with
  | entry => exact ⟨[], .entry, rfl⟩
  | step _ hb' ht' ih =>
    obtain ⟨prev, hp, rfl⟩ := ih
    rw [function_getElem?, Option.map_eq_some_iff] at hb'
    obtain ⟨blk, hb, rfl⟩ := hb'
    exact ⟨prev ++ [blk], .step hp hb ht', by simp⟩

lemma mem_blocks {fn : Function} {b' : Block} (h : b' ∈ fn.removeNoops.blocks) :
    ∃ b ∈ fn.blocks, b' = b.removeNoops := by
  obtain ⟨b, hb, rfl⟩ := Array.mem_map.1 h
  exact ⟨b, hb, rfl⟩

lemma mem_ops {b : Block} {op : Operation VarId} (h : op ∈ b.removeNoops.ops) : op ∈ b.ops :=
  (Array.mem_filter.1 h).1

lemma function_wf {fn : Function} (hwf : fn.WF) : fn.removeNoops.WF where
  entry_valid := by
    simpa [Function.ValidBlockId, Function.removeNoops] using hwf.entry_valid
  ssa := by rw [function_defs]; exact hwf.ssa
  definedBeforeUse prev' b blk' hp' hb' := by
    obtain ⟨prev, hp, rfl⟩ := pathTo_back hp'
    rw [function_getElem?, Option.map_eq_some_iff] at hb'
    obtain ⟨blk, hb, rfl⟩ := hb'
    rw [List.flatMap_map]
    simp only [block_defs]
    exact definedBeforeUse (hwf.definedBeforeUse prev b blk hp hb)
  validTargets b' hb' t ht := by
    obtain ⟨b, hb, rfl⟩ := mem_blocks hb'
    obtain ⟨tb, htb, hsz⟩ := hwf.validTargets b hb t ht
    exact ⟨tb.removeNoops, by rw [function_getElem?, htb]; rfl, hsz⟩
  iretArity b' hb' hc := by
    obtain ⟨b, hb, rfl⟩ := mem_blocks hb'
    exact hwf.iretArity b hb hc

lemma callee_map {g : FunctionId} {n : Nat} {ret : ReturnKind} (h : p.Callee g n ret) :
    p.removeNoops.Callee g n ret := by
  obtain ⟨fn, hg, hret, e, he, hin⟩ := h
  refine ⟨fn.removeNoops, by rw [program_getElem?, hg]; rfl, hret, e.removeNoops, ?_, hin⟩
  rw [function_getElem?]
  show Option.map Block.removeNoops fn[fn.entry]? = _
  rw [he]
  rfl

lemma calls_back {b : Block} {g : FunctionId} (h : b.removeNoops.Calls g) : b.Calls g := by
  rcases h with ⟨op, hop, hc⟩ | hc
  · exact .inl ⟨op, mem_ops hop, hc⟩
  · exact .inr hc

lemma callEdge_back {f g : FunctionId} (h : p.removeNoops.CallEdge f g) : p.CallEdge f g := by
  obtain ⟨fn', hfn', prev', b, blk', hp', hb', hc'⟩ := h
  rw [program_getElem?, Option.map_eq_some_iff] at hfn'
  obtain ⟨fn, hfn, rfl⟩ := hfn'
  obtain ⟨prev, hp, rfl⟩ := pathTo_back hp'
  rw [function_getElem?, Option.map_eq_some_iff] at hb'
  obtain ⟨blk, hb, rfl⟩ := hb'
  exact ⟨fn, hfn, prev, b, blk, hp, hb, calls_back hc'⟩

lemma reachable_back {r f : FunctionId} (h : p.removeNoops.Reachable r f) : p.Reachable r f := by
  induction h with
  | root => exact .root
  | call _ he ih => exact .call ih (callEdge_back he)

lemma transGen_back {a b : FunctionId} (h : Relation.TransGen p.removeNoops.CallEdge a b) :
    Relation.TransGen p.CallEdge a b := by
  induction h with
  | single he => exact .single (callEdge_back he)
  | tail _ he ih => exact .tail ih (callEdge_back he)

lemma validFrom {k : ExecutionModeKind} {r : FunctionId} (h : p.ValidFrom k r) :
    p.removeNoops.ValidFrom k r := by
  intro f fn' hr hf' prev' b blk' hp' hb' op hop
  rw [program_getElem?, Option.map_eq_some_iff] at hf'
  obtain ⟨fn, hfn, rfl⟩ := hf'
  obtain ⟨prev, hp, rfl⟩ := pathTo_back hp'
  rw [function_getElem?, Option.map_eq_some_iff] at hb'
  obtain ⟨blk, hb, rfl⟩ := hb'
  have := h f fn (reachable_back hr) hfn prev b blk hp hb op (mem_ops hop)
  cases op <;> exact this

lemma removeNoops_wf (hwf : p.WF) : p.removeNoops.WF where
  functions fn' hfn' := by
    obtain ⟨fn, hfn, rfl⟩ := Array.mem_map.1 hfn'
    exact function_wf (hwf.functions fn hfn)
  validCalls fn' hfn' b' hb' := by
    obtain ⟨fn, hfn, rfl⟩ := Array.mem_map.1 hfn'
    obtain ⟨b, hb, rfl⟩ := mem_blocks hb'
    have hv := hwf.validCalls fn hfn b hb
    refine ⟨fun op hop => ?_, ?_⟩
    · have := hv.1 op (mem_ops hop)
      cases op with
      | icall g ins outs => exact callee_map this
      | _ => trivial
    · have := hv.2
      simp only [Block.removeNoops]
      cases h : b.control with
      | icallNever g ins => rw [h] at this; exact callee_map this
      | _ => trivial
  initEntry := callee_map hwf.initEntry
  mainEntry := callee_map hwf.mainEntry
  initOps := validFrom hwf.initOps
  mainOps := validFrom hwf.mainOps
  acyclicCalls f h := hwf.acyclicCalls f (transGen_back h)

end WF

end Sir.Proofs.RemoveNoops
