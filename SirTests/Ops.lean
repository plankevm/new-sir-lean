import Sir

/-! Pure EVM operations and Keccak-256 against known values (Keccak vectors from `cast keccak`). -/

namespace SirTests.Ops

def w (n : Nat) : Word := BitVec.ofNat 256 n
def neg (n : Nat) : Word := 0 - w n
def intMin : Word := w (2 ^ 255)
def max : Word := BitVec.allOnes 256

def bytes (l : List Nat) : ByteArray := ⟨(l.map Nat.toUInt8).toArray⟩

def checks : List (String × Bool) :=
  [ ("add wraps", max + 1 == 0),
    ("div by zero", Word.div 5 0 == 0),
    ("mod by zero", Word.mod 5 0 == 0),
    ("sdiv -10 3", Word.sdiv (neg 10) 3 == neg 3),
    ("sdiv intMin -1", Word.sdiv intMin (neg 1) == intMin),
    ("smod -10 3", Word.smod (neg 10) 3 == neg 1),
    ("smod by zero", Word.smod (neg 10) 0 == 0),
    ("addmod overflow", Word.addmod max 2 10 == 7),
    ("mulmod overflow", Word.mulmod max max 12 == 9),
    ("addmod mod zero", Word.addmod 1 2 0 == 0),
    ("exp 3 3", Word.exp 3 3 == 27),
    ("exp 2 255", Word.exp 2 255 == intMin),
    ("exp 2 256", Word.exp 2 256 == 0),
    ("exp 0 0", Word.exp 0 0 == 1),
    ("signextend 0 0xff", Word.signextend 0 0xff == max),
    ("signextend 0 0x7f", Word.signextend 0 0x7f == 0x7f),
    ("signextend 1 0x8000", Word.signextend 1 0x8000 == max <<< 16 ||| 0x8000),
    ("signextend 31", Word.signextend 31 0x80 == 0x80),
    ("lt", Word.lt 1 2 == 1 && Word.lt 2 1 == 0),
    ("gt", Word.gt 2 1 == 1),
    ("slt -1 0", Word.slt (neg 1) 0 == 1),
    ("sgt 0 -1", Word.sgt 0 (neg 1) == 1),
    ("byte 31", Word.byte 31 0x1234 == 0x34),
    ("byte 30", Word.byte 30 0x1234 == 0x12),
    ("byte 32", Word.byte 32 0x1234 == 0),
    ("shl 1 1", Word.shl 1 1 == 2),
    ("shl 256", Word.shl 256 1 == 0),
    ("shr huge", Word.shr max max == 0),
    ("shr 4", Word.shr 4 0xf0 == 0xf),
    ("sar 4 -16", Word.sar 4 (neg 16) == neg 1),
    ("sar huge negative", Word.sar max (neg 1) == max),
    ("sar huge positive", Word.sar max 5 == 0),
    ("clz 0", Word.clz 0 == 256),
    ("clz 1", Word.clz 1 == 255),
    ("clz 2^255", Word.clz intMin == 0),
    ("BinOp.eval sub is top - next", Sir.BinOp.eval .sub 10 3 == 7),
    ("BinOp.eval shl shifts the second input", Sir.BinOp.eval .shl 4 1 == 16),
    ("BinOp.eval byte indexes the second input", Sir.BinOp.eval .byte 31 0x1234 == 0x34),
    ("TernOp.eval addmod a b n", Sir.TernOp.eval .addmod 10 3 4 == 1),
    ("UnOp.eval not", Sir.UnOp.eval .not 0 == max),
    ("toBytes 2", (Word.toBytes 2 0x12345).toList == [0x23, 0x45]),
    ("ofBytes", Word.ofBytes (bytes [1, 2]) == 0x0102),
    ("slicePad", ((bytes [1, 2, 3]).slicePad 1 4).toList == [2, 3, 0, 0]),
    ("keccak empty", Word.keccak256 .empty
      == 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470),
    ("keccak abc", Word.keccak256 (bytes [0x61, 0x62, 0x63])
      == 0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45),
    ("keccak 32 zeros", Word.keccak256 (bytes (List.replicate 32 0))
      == 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563),
    ("keccak 136 bytes (padding block)", Word.keccak256 (bytes (List.range 136))
      == 0x7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e),
    ("keccak 200 bytes (two blocks)", Word.keccak256 (bytes (List.range 200))
      == 0xbfb0aa97863e797943cf7c33bb7e880bb4543f3d2703c0923c6901c2af57b890) ]

#eval show IO Unit from do
  let failed := checks.filter (!·.2)
  unless failed.isEmpty do
    throw (IO.userError s!"op checks failed: {failed.map (·.1)}")
  IO.println s!"{checks.length} op checks passed"

end SirTests.Ops
