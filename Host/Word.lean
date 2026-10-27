import Lint.BinderScope
/-! EVM words and the pure EVM operations on them. -/

universe u

structure ByteSize where
  bytes : Nat
  valid : 1 ≤ bytes ∧ bytes ≤ 32 := by decide
  deriving DecidableEq

def ByteSize.bits (s : ByteSize) : Nat := s.bytes * 8

abbrev Word := BitVec 256

def FiniteCardinality (α : Type u) (size : Nat) : Prop :=
  ∃ D : List α, D.length = size ∧ D.Nodup ∧ ∀ w, w ∈ D

namespace Word

def bits := 256

def ofNat (n : Nat) : Word := BitVec.ofNat bits n

def size : Nat := 2^bits

def has_size (x : Word) (s : ByteSize) : Prop :=
  x.toNat < 2 ^ s.bits

def lowBits (n : Nat) (w : Word) : Word := (w.setWidth n).setWidth bits

private def mkD : Nat → List Word
  | 0 => []
  | n+1 => (n : Word) :: mkD n

theorem valid_index_iff_mem {α : Type u} {l : List α} (x : α) : (∃ i : Nat, l[i]? = some x) ↔ (x ∈ l) :=
  List.mem_iff_getElem?.symm

theorem ofNat_eq_iff_eq_toNat {n : Nat} {w : Word} : n < size → (↑n = w ↔ n = w.toNat) := by
  intro h
  rw [← BitVec.toNat_inj, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n < 2 ^ 256 from h)]

theorem size_is_domain : FiniteCardinality Word size := by
  have : ∀ n ≤ size, (mkD n).length = n ∧ (mkD n).Nodup ∧ ∀ w, w ∈ mkD n ↔ w.toNat < n := by
    intro n hn
    induction n with
    | zero => simp [mkD]
    | succ n ih =>
      have ⟨hl, hd, hm⟩ := ih (by omega)
      have he : ∀ w : Word, (n : Word) = w ↔ n = w.toNat := fun _ => ofNat_eq_iff_eq_toNat (by omega)
      refine ⟨by simp [mkD, hl],
        List.nodup_cons.2 ⟨by rw [hm, ← (he _).1 rfl]; exact Nat.lt_irrefl n, hd⟩, fun w => ?_⟩
      simp only [mkD, List.mem_cons, hm, eq_comm (a := w), he]
      omega
  have ⟨hl, hd, hm⟩ := this size (Nat.le_refl _)
  exact ⟨mkD size, hl, hd, fun w => (hm w).2 w.isLt⟩

theorem lowBits_lt (n : Nat) (w : Word) : (Word.lowBits n w).toNat < 2 ^ n := by
  simp only [Word.lowBits, bits, BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))

def ofBool (b : Bool) : Word := if b then 1 else 0

/-- The low `n` bytes of `w`, big-endian. -/
def toBytes (n : Nat) (w : Word) : ByteArray :=
  ⟨(Array.range n).map fun i => (w.toNat >>> (8 * (n - 1 - i))).toUInt8⟩

/-- Big-endian bytes as a word, keeping the low 256 bits. -/
def ofBytes (b : ByteArray) : Word :=
  ofNat (b.data.foldl (fun acc x => acc * 256 + x.toNat) 0)

def div (a b : Word) : Word := if b = 0 then 0 else a / b

def sdiv (a b : Word) : Word := if b = 0 then 0 else BitVec.sdiv a b

def mod (a b : Word) : Word := if b = 0 then 0 else a % b

def smod (a b : Word) : Word := if b = 0 then 0 else BitVec.srem a b

def addmod (a b n : Word) : Word :=
  if n = 0 then 0 else ofNat ((a.toNat + b.toNat) % n.toNat)

def mulmod (a b n : Word) : Word :=
  if n = 0 then 0 else ofNat ((a.toNat * b.toNat) % n.toNat)

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

def clz (x : Word) : Word := if x = 0 then 256 else ofNat (255 - x.toNat.log2)

end Word

/-- A 160-bit account address. -/
abbrev Address := BitVec 160

namespace Address

def toWord (a : Address) : Word := a.setWidth 256

/-- The low 160 bits, as the EVM reads an address operand. -/
def ofWord (w : Word) : Address := w.setWidth 160

@[simp] theorem ofWord_toWord (a : Address) : ofWord a.toWord = a := by
  simp [ofWord, toWord]

theorem toWord_injective : Function.Injective toWord := fun a b h => by
  rw [← ofWord_toWord a, h, ofWord_toWord]

theorem toWord_lt (a : Address) : a.toWord.toNat < 2 ^ 160 := by
  simp only [toWord, BitVec.toNat_setWidth]
  omega

end Address

/-- `len` bytes of `b` from `off`, zero past its end (calldata/code/returndata reads). -/
def ByteArray.slicePad (b : ByteArray) (off len : Nat) : ByteArray :=
  ⟨(Array.range len).map fun i => if h : off + i < b.size then b[off + i] else 0⟩
