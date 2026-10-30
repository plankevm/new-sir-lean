import Sir.Ir
import Host.Effect

namespace Sir

def MainImmutablesMap (p : Program) : Type := (i : Fin p.immutables.size) → { v : Word // v.HasSize p.immutables[i] }

/-- The values `getimmutable` reads: fixed for a whole run, one per immutable, each fitting the
immutable's declared size. -/
inductive Immutables (p : Program) : Host.ExecutionModeKind → Type
  | init : Immutables p .creation
  | main : MainImmutablesMap p → Immutables p .call

def Immutables.values {p : Program} : (imm : Immutables p .call) → MainImmutablesMap p
  | .main m => m

instance {p : Program} : GetElem? (Immutables p .call) ImmutableId Word (fun _ => p.ValidImmutableId) where
  getElem imm i valid := (imm.values ⟨i.id, valid⟩).val
  getElem? imm i :=
    if h : i.id < p.immutables.size
    then some <| imm.values ⟨i.id, h⟩
    else .none

/-- Immutable `i` takes the low bytes of `ws[i]` (0 if absent). -/
def Immutables.ofWords (p : Program) (ws : Array Word) (h : ws.size = p.immutables.size) : Immutables p .call :=
  .main fun i =>
    ⟨ws[i].lowBits p.immutables[i].asBits, by {
      simp [Word.HasSize]
      exact (Word.lowBits_lt _ _)
    }⟩

abbrev MappingOffset (container bytes : ByteArray) : Type :=
  { offset : UInt32 // ∀ i, (h : i < bytes.size) → container[offset.toNat + i]? = some bytes[i] }

def MappingOffset.range {c b : ByteArray} (o : MappingOffset c b) : NatRange := ⟨o.val.toNat, b.size⟩

def zeros (size : ByteSize) : ByteArray := ⟨Array.replicate size.toNat 0⟩

/-- Facts about the compiled bytecode that SIR can observe. They are fixed by the compiler, not
by the environment, so they are a parameter of the semantics rather than effects. -/
structure Layout (p : Program) where
  init : ByteArray
  init_u32 : init.size < UInt32.size

  main : ByteArray
  main_u32 : main.size < UInt32.size

  mainStartOffset : MappingOffset init main
  initDataOffsets : (i : Fin p.data.size) → MappingOffset init p.data[i]
  mainDataOffsets : (i : Fin p.data.size) → i ∈ p.mainDatas → MappingOffset main p.data[i]

  immutableOffsets : (i : Fin p.immutables.size) → List (MappingOffset main (zeros p.immutables[i]))

  atLeastOne_immOffsets : ∀ i, (immutableOffsets i).length > 0
  no_imm_imm_overlap :
    ∀ i i',
    ∀ mo : Fin (immutableOffsets i).length,
    ∀ mo' : Fin (immutableOffsets i').length,
      (i = i' ∧ mo ≍ mo') ∨
      NatRange.Disjoint
        (immutableOffsets i)[mo].range
        (immutableOffsets i')[mo'].range
  no_imm_data_overlap :
    ∀ data im h,
    ∀ imo ∈ immutableOffsets im,
      NatRange.Disjoint
        imo.range
        (mainDataOffsets data h).range

end Sir
