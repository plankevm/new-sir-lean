import Host.Word

/-! Keccak-256 (the pre-standard padding used by the EVM), in pure Lean. -/

namespace Sir.Keccak

def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets, indexed by `x + 5 * y`. -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

def rotl (x n : UInt64) : UInt64 := (x <<< n) ||| (x >>> (64 - n))

def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let c := Array.ofFn (n := 5) fun x =>
    a[x]! ^^^ a[x.val + 5]! ^^^ a[x.val + 10]! ^^^ a[x.val + 15]! ^^^ a[x.val + 20]!
  let d := Array.ofFn (n := 5) fun x => c[(x.val + 4) % 5]! ^^^ rotl c[(x.val + 1) % 5]! 1
  let a := Array.ofFn (n := 25) fun i => a[i]! ^^^ d[i.val % 5]!
  let mut b := Array.replicate 25 (0 : UInt64)
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a[x + 5 * y]! rotations[x + 5 * y]!)
  let a := Array.ofFn (n := 25) fun i =>
    let x := i.val % 5
    let y := i.val / 5
    b[i]! ^^^ (~~~b[(x + 1) % 5 + 5 * y]! &&& b[(x + 2) % 5 + 5 * y]!)
  return a.set! 0 (a[0]! ^^^ rc)

def permute (a : Array UInt64) : Array UInt64 := roundConstants.foldl round a

def rate : Nat := 136

def pad (m : ByteArray) : ByteArray :=
  let n := rate - m.size % rate
  let p := (Array.replicate n (0 : UInt8)).modify 0 (· ^^^ 0x01) |>.modify (n - 1) (· ^^^ 0x80)
  m ++ ⟨p⟩

def lane (b : ByteArray) (off : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc k => acc ||| (b[off + k]!.toUInt64 <<< (8 * k).toUInt64)) 0

def hash (m : ByteArray) : ByteArray :=
  let p := pad m
  let state := (List.range (p.size / rate)).foldl (init := Array.replicate 25 (0 : UInt64))
    fun st blk => permute (Array.ofFn (n := 25) fun i =>
      if i.val < rate / 8 then st[i]! ^^^ lane p (blk * rate + 8 * i.val) else st[i]!)
  ⟨(Array.range 32).map fun i => (state[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8⟩

end Sir.Keccak

def Word.keccak256 (m : ByteArray) : Word := Word.ofBytes (Sir.Keccak.hash m)
