import SirTests.Same
import Sir

/-! `InitValid` on small programs, run by the kernel on concrete layouts. -/

namespace SirTests.Deploy

open Sir Host CoFree SirTests.Same

def deployProg (init main : Array Block) (immutables : Array ByteSize := #[]) : Program :=
  { init := 0, main := some 1, functions := #[⟨0, .never, init⟩, ⟨0, .never, main⟩], immutables }

def stopMain : Array Block := #[{ control := .stop }]

/-- A layout with no data, the runtime code `main` at `pre.size` in the init code, and every
immutable at `refs`. -/
def layoutOf (pre main : ByteArray) (refs : List Nat) : Layout where
  dataOffset _ _ := 0
  runtimeStartOffset := Word.ofNat pre.size
  initEndOffset := Word.ofNat (pre.size + main.size)
  runtimeLength := Word.ofNat main.size
  immutableRefs _ := refs

/-! ## Returning code not copied from the init code -/

/-- Returns `runtimeLength` zero bytes: not the runtime code. -/
def zeros : Program := deployProg (main := stopMain) #[
  { ops := #[.let 1 .runtimeLength, .let 2 (.malloc 1)], control := .return 2 1 }]

def zerosCode : Code zeros where
  layout := layoutOf ⟨#[0x60]⟩ ⟨#[0xFE, 0xAA]⟩ []
  init := ⟨#[0x60, 0xFE, 0xAA]⟩
  main := ⟨#[0xFE, 0xAA]⟩
  consistent := ⟨rfl, by decide +kernel, nofun, nofun⟩
  embedded := by decide +kernel
  slotsDisjoint := by decide +kernel
  dataOutsideSlots := nofun

theorem zeros_not_initValid : ¬zeros.InitValid := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 (h zerosCode zerosCode testEnv .empty default))
  have h := Same.branchL_inv h
    (observe_of_headBr (c := .placement 2 [] ⟨0, by decide⟩) (by kernel_rfl)) ⟨0, by decide⟩
  have h := Same.branchR_inv h
    (observe_of_headBr (c := .placement 2 [] ⟨0, by decide⟩) (by kernel_rfl)) ⟨0, by decide⟩
  have h := skipR_inv 100 (skipL_inv 100 h)
  have h := Same.ret_inv h (a := .ret ⟨#[0, 0]⟩ default) (b := .ret ⟨#[0, 0]⟩ default)
    (by kernel_rfl) (by kernel_rfl)
  obtain ⟨_, _, _, hx, _⟩ := h
  have : zerosCode.extract ⟨#[0, 0]⟩ = none := by kernel_rfl
  rw [this] at hx
  cases hx

/-! ## Branching on the runtime code's bytes -/

def b8 : ByteSize := ⟨1, by decide⟩

/-- Copies the first byte of the runtime code and halts by `invalid` if it is zero, else reverts. -/
def peeks : Program := deployProg (main := stopMain) #[
  { ops := #[.let 1 (.const 1), .let 2 (.malloc 1), .let 3 .runtimeStartOffset,
      .stmt (.codecopy 2 3 1), .let 4 (.mload b8 2), .let 5 (.const 0)],
    control := .branches 4 1 2 },
  { control := .revert 5 5 },
  { control := .invalid }]

def peeksCode0 : Code peeks where
  layout := layoutOf ⟨#[0x60]⟩ ⟨#[0, 0xAA]⟩ []
  init := ⟨#[0x60, 0, 0xAA]⟩
  main := ⟨#[0, 0xAA]⟩
  consistent := ⟨rfl, by decide +kernel, nofun, nofun⟩
  embedded := by decide +kernel
  slotsDisjoint := by decide +kernel
  dataOutsideSlots := nofun

def peeksCode1 : Code peeks where
  layout := layoutOf ⟨#[0x60]⟩ ⟨#[1, 0xAA]⟩ []
  init := ⟨#[0x60, 1, 0xAA]⟩
  main := ⟨#[1, 0xAA]⟩
  consistent := ⟨rfl, by decide +kernel, nofun, nofun⟩
  embedded := by decide +kernel
  slotsDisjoint := by decide +kernel
  dataOutsideSlots := nofun

/-- Two layouts whose runtime codes differ in a byte `init` branches on. -/
theorem peeks_not_initValid : ¬peeks.InitValid := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 (h peeksCode0 peeksCode1 testEnv .empty default))
  have h := Same.branchL_inv h
    (observe_of_headBr (c := .placement 1 [] ⟨0, by decide⟩) (by kernel_rfl)) ⟨0, by decide⟩
  have h := Same.branchR_inv h
    (observe_of_headBr (c := .placement 1 [] ⟨0, by decide⟩) (by kernel_rfl)) ⟨0, by decide⟩
  have h := skipR_inv 100 (skipL_inv 100 h)
  nomatch Same.ret_inv h (a := .invalid) (b := .revert .empty) (by kernel_rfl) (by kernel_rfl)

/-! ## An immutable holding where the appended data starts

`init` copies the runtime code, appends a word, and stores the runtime code's length (where the
word starts) in immutable 0. `main` stores the length of the appended data, `codesize` minus that
immutable. The immutable differs between layouts, but `main` behaves the same. -/

def tailOffset : Program := deployProg (immutables := #[⟨2, by decide⟩])
  #[{ ops := #[.let 1 .runtimeLength, .let 2 (.const 32), .let 3 (.binop .add 1 2),
        .let 4 (.malloc 3), .let 5 .runtimeStartOffset, .stmt (.codecopy 4 5 1),
        .let 6 (.binop .add 4 1), .let 7 (.const 0x2A), .stmt (.mstore ⟨32, by decide⟩ 6 7),
        .stmt (.setImmutable 0 4 1)],
      control := .return 4 3 }]
  #[{ ops := #[.let 1 (.getImmutable 0), .let 2 .codesize, .let 3 (.binop .sub 2 1),
        .let 4 (.const 0), .stmt (.sstore 4 3)],
      control := .stop }]

/-- A 6-byte runtime code with its slot (junk `EE EE`) at 2. -/
def tailCode₁ : Code tailOffset where
  layout := layoutOf ⟨#[0x60, 0x61]⟩ ⟨#[0xA1, 0xA2, 0xEE, 0xEE, 0xA5, 0xA6]⟩ [2]
  init := ⟨#[0x60, 0x61, 0xA1, 0xA2, 0xEE, 0xEE, 0xA5, 0xA6]⟩
  main := ⟨#[0xA1, 0xA2, 0xEE, 0xEE, 0xA5, 0xA6]⟩
  consistent := by
    refine ⟨rfl, by decide +kernel, nofun, fun ⟨i⟩ hi r hr => ?_⟩
    obtain rfl : i = 0 := by simpa [tailOffset, deployProg] using hi
    obtain rfl : r = 2 := by simpa [layoutOf] using hr
    revert hi; decide +kernel
  embedded := by decide +kernel
  slotsDisjoint := by decide +kernel
  dataOutsideSlots := nofun

/-- An 8-byte runtime code with its slot at 1, after a shorter init prefix. -/
def tailCode₂ : Code tailOffset where
  layout := layoutOf ⟨#[0x61]⟩ ⟨#[0xB1, 0xEE, 0xEE, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8]⟩ [1]
  init := ⟨#[0x61, 0xB1, 0xEE, 0xEE, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8]⟩
  main := ⟨#[0xB1, 0xEE, 0xEE, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8]⟩
  consistent := by
    refine ⟨rfl, by decide +kernel, nofun, fun ⟨i⟩ hi r hr => ?_⟩
    obtain rfl : i = 0 := by simpa [tailOffset, deployProg] using hi
    obtain rfl : r = 1 := by simpa [layoutOf] using hr
    revert hi; decide +kernel
  embedded := by decide +kernel
  slotsDisjoint := by decide +kernel
  dataOutsideSlots := nofun

/-- What `init` returns from `tailCode₁`: the runtime code with 6 in the slot, then the word. -/
def tailRet₁ : ByteArray := ⟨#[0xA1, 0xA2, 0x00, 0x06, 0xA5, 0xA6, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2A]⟩

def tailRet₂ : ByteArray := ⟨#[0xB1, 0x00, 0x08, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2A]⟩

def pureOf? {A : Type} (t : CoFree Exec SirND A) : Option A :=
  match t.observe with
  | .pure a => some a
  | _ => none

theorem same_of_pureOf {A : Type} {x y : CoFree Exec SirND A} {a : A} (hx : pureOf? x = some a)
    (hy : pureOf? y = some a) : Same Eq x y := by
  unfold pureOf? at hx hy
  split at hx <;> split at hy <;> try cases hx
  all_goals try cases hy
  exact Same.ret ‹_› ‹_› rfl

/-- `main` stores 32, the length of the appended word, under both layouts. -/
theorem tailOffset_main_same (st : Store) :
    DeployRel tailOffset tailCode₁ tailCode₂ (.ret tailRet₁ st) (.ret tailRet₂ st) := by
  refine ⟨rfl, .ofWords tailOffset #[6], .ofWords tailOffset #[8], ?_, ?_, fun env s => ?_⟩
  · kernel_rfl
  · kernel_rfl
  rcases env with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, static⟩
  apply same_skipL 100; apply same_skipR 100
  cases static
  · exact same_of_pureOf (a := .ret .empty ⟨s.store.storage.set 0 32, s.store.transient⟩)
      (by kernel_rfl) (by kernel_rfl)
  · exact same_of_pureOf (a := .invalid) (by kernel_rfl) (by kernel_rfl)

theorem tailOffset_branches₁ (env : Env) (s : State) :
    headBr (skip 100 (runInit tailOffset tailCode₁ env .empty s)) =
      some (.placement 38 [] ⟨0, by decide⟩) := by kernel_rfl

theorem tailOffset_branches₂ (env : Env) (s : State) :
    headBr (skip 100 (runInit tailOffset tailCode₂ env .empty s)) =
      some (.placement 40 [] ⟨0, by decide⟩) := by kernel_rfl

/-- With both allocations placed at 0, the two runs of `init` are related. -/
theorem tailOffset_at_zero (env : Env) (s : State) :
    Same (DeployRel tailOffset tailCode₁ tailCode₂)
      (resumeBr (skip 100 (runInit tailOffset tailCode₁ env .empty s))
        (.placement 38 [] ⟨0, by decide⟩) ⟨0, by decide⟩)
      (resumeBr (skip 100 (runInit tailOffset tailCode₂ env .empty s))
        (.placement 40 [] ⟨0, by decide⟩) ⟨0, by decide⟩) := by
  apply same_skipL 100; apply same_skipR 100
  exact Same.ret (a := .ret tailRet₁ s.store) (b := .ret tailRet₂ s.store) (by kernel_rfl)
    (by kernel_rfl) (tailOffset_main_same _)

/-- The immutable differs between the layouts, so `init` is not `InitPlain`: `InitValid` is
strictly weaker. -/
theorem tailOffset_not_initPlain : ¬tailOffset.InitPlain := by
  intro h
  have h := skipR_inv 100 (skipL_inv 100 (h tailCode₁ tailCode₂ testEnv .empty default))
  have h := Same.branchL_inv h (observe_of_headBr (tailOffset_branches₁ _ _)) ⟨0, by decide⟩
  have h := Same.branchR_inv h (observe_of_headBr (tailOffset_branches₂ _ _)) ⟨0, by decide⟩
  have h := skipR_inv 100 (skipL_inv 100 h)
  obtain ⟨_, _, imm, h₁, h₂⟩ :=
    Same.ret_inv h (a := .ret tailRet₁ default) (b := .ret tailRet₂ default) (by kernel_rfl)
      (by kernel_rfl)
  have e₁ : tailCode₁.extract tailRet₁ = some (.ofWords tailOffset #[6]) := by kernel_rfl
  have e₂ : tailCode₂.extract tailRet₂ = some (.ofWords tailOffset #[8]) := by kernel_rfl
  rw [e₁] at h₁; rw [e₂] at h₂
  have := congrArg (fun i : Immutables tailOffset => (i.values ⟨0, by decide⟩).val)
    (Option.some.inj (h₁.trans h₂.symm))
  revert this; decide +kernel

/-! ## Reading immutables back -/

/-- Immutable 0 patched in twice, at 0 and 3. -/
def twoSlots : Code tailOffset where
  layout := layoutOf ⟨#[0x60]⟩ ⟨#[0xEE, 0xEE, 0xA2, 0xEE, 0xEE]⟩ [0, 3]
  init := ⟨#[0x60, 0xEE, 0xEE, 0xA2, 0xEE, 0xEE]⟩
  main := ⟨#[0xEE, 0xEE, 0xA2, 0xEE, 0xEE]⟩
  consistent := by
    refine ⟨rfl, by decide +kernel, nofun, fun ⟨i⟩ hi r hr => ?_⟩
    obtain rfl : i = 0 := by simpa [tailOffset, deployProg] using hi
    rcases (by simpa [layoutOf] using hr : r = 0 ∨ r = 3) with rfl | rfl <;> (revert hi; decide +kernel)
  embedded := by decide +kernel
  slotsDisjoint := by decide +kernel
  dataOutsideSlots := nofun

theorem twoSlots_agree : twoSlots.extract ⟨#[0, 7, 0xA2, 0, 7]⟩ = some (.ofWords tailOffset #[7]) := by
  kernel_rfl

/-- The copies of an immutable disagree. -/
theorem twoSlots_disagree : twoSlots.extract ⟨#[0, 7, 0xA2, 0, 8]⟩ = none := by kernel_rfl

/-- A byte outside the slots changed. -/
theorem twoSlots_changed : twoSlots.extract ⟨#[0, 7, 0xA3, 0, 7]⟩ = none := by kernel_rfl

/-- The runtime code is cut short. -/
theorem twoSlots_short : twoSlots.extract ⟨#[0, 7, 0xA2, 0]⟩ = none := by kernel_rfl

end SirTests.Deploy
