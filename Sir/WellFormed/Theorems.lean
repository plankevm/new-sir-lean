import Sir.WellFormed.Proofs

open Host CoFree

namespace Sir

theorem Block.definedBeforeUse_mono :
    ∀ (b : Block) (pre pre' : List VarId),
      pre ⊆ pre' → b.DefinedBeforeUse pre → b.DefinedBeforeUse pre' :=
  Proofs.definedBeforeUse_mono

theorem Program.runMain_not_malformed :
    ∀ (p : Program) (l : Layout p) (imms : MainImmutables) (static : Bool) (cd : BytesX32) (e : Env) (w₀ : World),
      p.WF → imms.WF p →
      ¬∃ r, HasResOutcome (p.runMain l imms static cd e w₀) (.inl (.malformed r)) :=
  Proofs.runMain_not_malformed

theorem Program.runInit_not_malformed :
    ∀ (p : Program) (l : Layout p) (c : ByteArray) (e : Env) (w₀ : World),
      p.WF → ¬∃ r, HasResOutcome (p.runInit l c e w₀) (.inl (.malformed r)) :=
  Proofs.runInit_not_malformed

theorem Program.runInit_ret_wf :
    ∀ (p : Program) (l : Layout p) (c : ByteArray) (e : Env) (w₀ : World) (imms : MainImmutables) (s' : Store),
      HasResOutcome (p.runInit l c e w₀) (.inr (.ret imms s')) → imms.WF p :=
  Proofs.runInit_ret_wf

theorem Program.deploy_main_not_malformed :
    ∀ (p : Program) (l : Layout p) (ctorArgs : ByteArray) (env : Env) (w₀ : World)
      (imms : MainImmutables) (store : Store) (static : Bool) (calldata : BytesX32) (env' : Env)
      (w₁ : World) (reason : String),
      p.WF →
      HasResOutcome (p.runInit l ctorArgs env w₀) (.inr (.ret imms store)) →
      ¬HasResOutcome (p.runMain l imms static calldata env' w₁) (.inl (.malformed reason)) :=
  Proofs.deploy_main_not_malformed

end Sir
