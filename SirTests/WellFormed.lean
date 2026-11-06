import SirTests.Safety.Defs
import Sir.WellFormed.Theorems

namespace SirTests.WF

open Sir

lemma noop_noCalls : ∀ fn ∈ Safety.noop.functions, ∀ b ∈ fn.blocks,
    (∀ op ∈ b.ops, op.callee? = none) ∧ b.control.callee? = none := by
  decide +kernel

lemma noop_noCallEdge : ∀ f g, ¬ Safety.noop.CallEdge f g := by
  rintro _ g ⟨fn, hf, b, hb, hc⟩
  obtain ⟨hops, hctrl⟩ := noop_noCalls _ (Array.mem_of_getElem? hf) _ hb
  rcases hc with ⟨op, hop, hg⟩ | hg
  · rw [hops op hop] at hg; cases hg
  · rw [hctrl] at hg; cases hg

lemma noop_reachable {root f : FunctionId} (h : Safety.noop.Reachable root f) : f = root := by
  cases h with
  | root => rfl
  | call _ he => exact (noop_noCallEdge _ _ he).elim

theorem noop_wf : Safety.noop.WF where
  functions fn hfn := by
    have hssa : ∀ fn ∈ Safety.noop.functions, fn.defs.Nodup := by decide +kernel
    have hdbu : ∀ fn ∈ Safety.noop.functions, ∀ b ∈ fn.blocks, b.DefinedBeforeUse [] := by
      decide +kernel
    have hentry : ∀ fn ∈ Safety.noop.functions, fn.entry.id < fn.blocks.size := by decide +kernel
    have htgt : ∀ fn ∈ Safety.noop.functions, ∀ b ∈ fn.blocks, b.control.targets = [] := by
      decide +kernel
    have hiret : ∀ fn ∈ Safety.noop.functions, ∀ b ∈ fn.blocks,
        (match b.control with | .iret => false | _ => true) = true := by
      decide +kernel
    refine ⟨hentry fn hfn, hssa fn hfn, fun prev _ b _ hb =>
      Block.definedBeforeUse_mono b [] _ (List.nil_subset _)
        (hdbu fn hfn b (Array.mem_of_getElem? hb)),
      fun b hb t ht => ?_, fun b hb hc => ?_⟩
    · rw [htgt fn hfn b hb] at ht; cases ht
    · have := hiret fn hfn b hb; rw [hc] at this; cases this
  validCalls fn hfn b hb := by
    obtain ⟨hops, hctrl⟩ := noop_noCalls fn hfn b hb
    refine ⟨fun op hop => ?_, ?_⟩
    · have := hops op hop
      cases op <;> first | trivial | cases this
    · cases h : b.control <;> rw [h] at hctrl <;> first | trivial | cases hctrl
  initEntry := ⟨_, rfl, rfl, _, rfl, rfl⟩
  mainEntry := ⟨_, rfl, rfl, _, rfl, rfl⟩
  initOps f fn hr hf b hb op hop := by
    obtain rfl := noop_reachable hr
    cases hf
    simp [Safety.noop, OfNat.ofNat] at hb
    subst hb
    simp at hop
    rcases hop with rfl | rfl | rfl | rfl <;> trivial
  mainOps f fn hr hf b hb op hop := by
    obtain rfl := noop_reachable hr
    cases hf
    simp [Safety.noop, OfNat.ofNat] at hb
    subst hb
    simp at hop
  acyclicCalls f h := by
    cases h with
    | single h => exact noop_noCallEdge _ _ h
    | tail _ h => exact noop_noCallEdge _ _ h

end SirTests.WF
