import Lint.BinderScope
/-- `len` bytes of `b` from `off`, zero past its end . -/
def ByteArray.slicePadded (b : ByteArray) (off len : Nat) : ByteArray :=
  ⟨(Array.range len).map fun i => if h : off + i < b.size then b[off + i] else 0⟩

abbrev BytesX32 := { d : ByteArray // d.size < UInt32.size }

def BytesX32.empty : BytesX32 := ⟨.empty, by decide⟩
