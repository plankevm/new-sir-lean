import Sir.Outcome
import Host.Outcome.Proofs

/-! Init does not depend on how the compiler lays out the bytecode.

A compiler places data segments, the runtime code and the immutable slots where it likes, and the
bytes of the runtime code are whatever it emits. `Code p` is any such bytecode: its layout and the
bytes of both code objects, every byte the layout does not fix being arbitrary. `InitValid p`
runs `init` on two of them, with the same environment, constructor arguments and state, and asks
that the runs be related by `CoFree.Same` with `DeployRel` on their outcomes (via
`Host.catchHalt`): both return a runtime code from which the immutables can be read back
(`Code.extract`), and `main` behaves the same on the two runtime codes.

`main` is compared rather than the immutables, so `init` may store layout-dependent values in
immutables (say, where its appended data starts) as long as `main` only uses them as such.
`InitPlain` is the stronger property that both runs return the same immutables and the same
appended data; `MainValid` is `main`'s own independence of the layout; together they give
`InitValid` (`Program.initValid_of_plain`). -/

namespace Sir

open Host CoFree

/-- Where the immutables are patched into the runtime code: every reference of every immutable,
with the immutable's size. -/
def Layout.slots (p : Program) (l : Layout) : List NatRange :=
  (List.finRange p.immutables.size).flatMap fun (i : Fin _) =>
    (l.immutableRefs ⟨i.val⟩).map fun r => ⟨r, p.immutables[i].val⟩

/-- Bytecode a compiler may emit for `p`: `init` is the init code object without the
constructor arguments, `main` the runtime code before the immutables are patched in. -/
structure Code (p : Program) where
  layout : Layout
  init : ByteArray
  main : ByteArray
  consistent : layout.Consistent p init main
  embedded : init.slicePad layout.runtimeStartOffset.toNat layout.runtimeLength.toNat = main
  slotsDisjoint : (layout.slots p).Pairwise NatRange.Disjoint
  dataOutsideSlots : ∀ (d : DataId) (h : d.id < p.data.size), ∀ s ∈ layout.slots p,
    NatRange.Disjoint ⟨(layout.dataOffset .main d).toNat, p.data[d.id].size⟩ s

namespace Code

variable {p : Program}

/-- The value in the slots of immutable `i`: all of them must hold the same one. -/
def immutable? (c : Code p) (r : ByteArray) (i : Fin p.immutables.size) : Option Word :=
  match (c.layout.immutableRefs ⟨i.val⟩).map fun ref =>
      Word.ofBytes (r.slicePad ref p.immutables[i].val) with
  -- No slot: the runtime code cannot hold a value, and both runs read the same one.
  | [] => some 0
  | w :: ws => if ws.all (· == w) then some w else none

/-- The immutables of a runtime code `r` that `init` returned, if `r` is `c.main` with only
its slots changed, followed by any appended data. -/
def extract (c : Code p) (r : ByteArray) : Option (Immutables p) := do
  guard (c.main.size ≤ r.size && (List.range c.main.size).all fun j =>
    (c.layout.slots p).any (fun s => s.start ≤ j && j < s.end) || r[j]! == c.main[j]!)
  let ws ← (List.finRange p.immutables.size).mapM (c.immutable? r)
  pure (.ofWords p ws.toArray)

/-- What `init` appended after the runtime code. -/
def tail (c : Code p) (r : ByteArray) : ByteArray := r.extract c.main.size r.size

end Code

/-- `init` deploying from `c`, with constructor arguments `args` appended to its code. -/
def runInit (p : Program) (c : Code p) (env : Env) (args : ByteArray) (s : State) :
    CoFree Exec SirND Outcome :=
  catchHalt (exec p c.layout (.ofWords p #[]) { env with code := c.init ++ args } .init s)

/-- `main` running the runtime code `code` that `init` returned from `c`. -/
def runMain (p : Program) (c : Code p) (imm : Immutables p) (code : ByteArray) (env : Env)
    (s : State) : CoFree Exec SirND Outcome :=
  catchHalt (exec p c.layout imm { env with code := code } .main s)

/-- How the outcomes of `init` from `c₁` and `c₂` must agree. Returned runtime codes must both
contain their `main`s, with the same storage left behind, and `main` must behave the same on them
in every later environment and state. Other outcomes are equal; UB is never related. -/
def DeployRel (p : Program) (c₁ c₂ : Code p) : Outcome → Outcome → Prop
  | .ret r₁ st₁, .ret r₂ st₂ => st₁ = st₂ ∧ ∃ i₁ i₂, c₁.extract r₁ = some i₁ ∧
      c₂.extract r₂ = some i₂ ∧ ∀ env s, Same Eq (runMain p c₁ i₁ r₁ env s) (runMain p c₂ i₂ r₂ env s)
  | .ub _, _ | _, .ub _ => False
  | o₁, o₂ => o₁ = o₂

def Program.InitValid (p : Program) : Prop :=
  ∀ (c₁ c₂ : Code p) env args s, Same (DeployRel p c₁ c₂) (runInit p c₁ env args s) (runInit p c₂ env args s)

/-- `main` behaves the same on any two runtime codes with the same immutables and the same
appended data, whatever their layouts. -/
def Program.MainValid (p : Program) : Prop :=
  ∀ (c₁ c₂ : Code p) (r₁ r₂ : ByteArray) imm, c₁.extract r₁ = some imm → c₂.extract r₂ = some imm →
    c₁.tail r₁ = c₂.tail r₂ → ∀ env s, Same Eq (runMain p c₁ imm r₁ env s) (runMain p c₂ imm r₂ env s)

/-- Like `DeployRel`, but returned runtime codes must have the same immutables and appended data. -/
def PlainRel (p : Program) (c₁ c₂ : Code p) : Outcome → Outcome → Prop
  | .ret r₁ st₁, .ret r₂ st₂ => st₁ = st₂ ∧ c₁.tail r₁ = c₂.tail r₂ ∧
      ∃ imm, c₁.extract r₁ = some imm ∧ c₂.extract r₂ = some imm
  | .ub _, _ | _, .ub _ => False
  | o₁, o₂ => o₁ = o₂

/-- `init` returns the same immutables and appended data whatever the layout. -/
def Program.InitPlain (p : Program) : Prop :=
  ∀ (c₁ c₂ : Code p) env args s, Same (PlainRel p c₁ c₂) (runInit p c₁ env args s) (runInit p c₂ env args s)

end Sir
