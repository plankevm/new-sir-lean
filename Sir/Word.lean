import Lint.BinderScope
/-! EVM words and the pure EVM operations on them. -/

structure ByteSize where
  val : Nat
  valid : 1 ≤ val ∧ val ≤ 32 := by decide
  deriving DecidableEq

def ByteSize.bits (s : ByteSize) : Nat := s.val * 8

abbrev Word := BitVec 256

namespace Word

def has_size (x : Word) (s : ByteSize) : Prop :=
  x.toNat < 2 ^ s.bits

def lowBits (n : Nat) (w : Word) : Word := (w.setWidth n).setWidth 256

theorem lowBits_lt (n : Nat) (w : Word) : (Word.lowBits n w).toNat < 2 ^ n := by
  simp only [Word.lowBits , BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))

def ofBool (b : Bool) : Word := if b then 1 else 0

/-- The low `n` bytes of `w`, big-endian. -/
def toBytes (n : Nat) (w : Word) : ByteArray :=
  ⟨(Array.range n).map fun i => (w.toNat >>> (8 * (n - 1 - i))).toUInt8⟩

/-- Big-endian bytes as a word, keeping the low 256 bits. -/
def ofBytes (b : ByteArray) : Word :=
  BitVec.ofNat 256 (b.data.foldl (fun acc x => acc * 256 + x.toNat) 0)

def div (a b : Word) : Word := if b = 0 then 0 else a / b

def sdiv (a b : Word) : Word := if b = 0 then 0 else BitVec.sdiv a b

def mod (a b : Word) : Word := if b = 0 then 0 else a % b

def smod (a b : Word) : Word := if b = 0 then 0 else BitVec.srem a b

def addmod (a b n : Word) : Word :=
  if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat)

def mulmod (a b n : Word) : Word :=
  if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)

def exp (base e : Word) : Word :=
  go 256 base e.toNat 1
where
  go : Nat → Word → Nat → Word → Word
    | 0, _, _, acc => acc
    | n + 1, b, e, acc => go n (b * b) (e / 2) (if e % 2 = 1 then acc * b else acc)

def signextend (b x : Word) : Word :=
  if b.toNat < 31 then
    let t := 8 * b.toNat + 7
    let mask : Word := (1 <<< (t + 1)) - 1
    if x.getLsbD t then x ||| ~~~mask else x &&& mask
  else x

def lt (a b : Word) : Word := ofBool (BitVec.ult a b)
def gt (a b : Word) : Word := ofBool (BitVec.ult b a)
def slt (a b : Word) : Word := ofBool (BitVec.slt a b)
def sgt (a b : Word) : Word := ofBool (BitVec.slt b a)
def eq (a b : Word) : Word := ofBool (a == b)
def iszero (a : Word) : Word := ofBool (a == 0)

def byte (i x : Word) : Word :=
  if i.toNat < 32 then (x >>> (8 * (31 - i.toNat))) &&& 0xff else 0

-- Shift amounts are compared first: shifting a `Nat` by a 256-bit amount would not terminate in practice.
def shl (shift x : Word) : Word := if shift.toNat < 256 then x <<< shift.toNat else 0

def shr (shift x : Word) : Word := if shift.toNat < 256 then x >>> shift.toNat else 0

def sar (shift x : Word) : Word :=
  if shift.toNat < 256 then x.sshiftRight shift.toNat
  else if x.msb then BitVec.allOnes 256 else 0

def clz (x : Word) : Word := if x = 0 then 256 else BitVec.ofNat 256 (255 - x.toNat.log2)

end Word

/-- `len` bytes of `b` from `off`, zero past its end (calldata/code/returndata reads). -/
def ByteArray.slicePad (b : ByteArray) (off len : Nat) : ByteArray :=
  ⟨(Array.range len).map fun i => if h : off + i < b.size then b[off + i] else 0⟩
