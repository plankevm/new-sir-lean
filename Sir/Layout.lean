import Sir.Ir
import Host.Effect

namespace Sir

structure MainImmutablesMap (p : Program) : Type where
  slots : Vector Word p.immutables.size
  tail : ByteArray
  slot_values_correctly_sized : ∀ i : Fin p.immutables.size, slots[i].HasSize p.immutables[i]

inductive Immutables (p : Program) : Host.ExecutionModeKind → Type
  | init : Immutables p .creation
  | main : MainImmutablesMap p → Immutables p .call

def Immutables.getMain {p : Program} : (imm : Immutables p .call) → MainImmutablesMap p
  | .main m => m

instance {p : Program} : GetElem? (Immutables p .call) ImmutableId Word (fun _ => p.ValidImmutableId) where
  getElem imm i valid := imm.getMain.slots[i.id]
  getElem? imm i := imm.getMain.slots[i.id]?

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


def Layout.withSetImmutables {p : Program} (l : Layout p) (imms : MainImmutablesMap p) : ByteArray
:= Id.run do
  let mut main := l.main
  for imm in List.finRange p.immutables.size do
    let value := imms.slots[imm].toBytes p.immutables[imm]
    for offset in l.immutableOffsets imm do
      main := ByteArray.copySlice value 0 main offset.val.toNat value.size
  return main ++ imms.tail

def Layout.extractImmutables {p : Program} (l : Layout p) (returnedMain : ByteArray)
  : Option (ByteArray × Array Word) := do
  guard (returnedMain.size ≥ l.main.size)
  let tail := returnedMain.extract l.main.size returnedMain.size
  let mut slots := Vector.replicate p.immutables.size .none
  have hs : p.immutables.size = slots.size := by grind

  for i in List.finRange p.immutables.size do
    for slot in l.immutableOffsets i do
      let offset := slot.val.toNat
      let value := Word.ofBytes (returnedMain.extract offset p.immutables[i].toNat)
      match slots[i] with
      | .some value' => guard (value = value')
      | .none => slots := slots.set i.val (.some value) i.isLt

  return (tail, ← slots.toArray.mapM id)

end Sir
