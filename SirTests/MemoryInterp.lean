import Sir.Memory

/-! `interpMem` runs: allocation picks a placement, bytes move, and out-of-bounds access is
returned as undefined behavior. -/

namespace SirTests.MemoryInterp

open Sir Host

/-- Runs `interpMem`'s machine, placing each allocation after every live one and filling it with
`0xAA`; stops on any host operation. -/
def runMem {A : Type 1} : Nat → CoFree.{0, 1} HostE MemoryND A → Option A
  | 0, _ => none
  | n + 1, t => match t.observe with
    | .pure a => some a
    | .silent t => runMem n t
    | .impure _ _ => none
    | .branch (.alloc size live) k =>
      let a : Allocation := ⟨Word.ofNat (live.foldl (fun e a => max e a.end) 0x80),
        ⟨.replicate size.toNat 0xAA⟩⟩
      if h : ValidAlloc live size.toNat a then runMem n (k ⟨some a, h⟩) else none

def result {α : Type} (p : SirM α) : Option (Except UB α) :=
  (runMem 1000 (interpMem p)).map (·.down)

def copyProg : SirM ByteArray := do
  let p : Word ← alloc_uninit 4
  let q : Word ← alloc_zeroed 4
  mem.write (p + 1) ⟨#[1, 2]⟩
  mem.copy ⟨q, p, 4⟩
  mem.read q 6

def inBoundsProg : SirM ByteArray := do
  let p : Word ← alloc_uninit 4
  let q : Word ← alloc_zeroed 4
  mem.write (p + 1) ⟨#[1, 2]⟩
  mem.copy ⟨q, p, 4⟩
  mem.read p 8

#guard (result inBoundsProg).map (·.toOption.map (·.toList)) ==
  some (some [0xAA, 1, 2, 0xAA, 0xAA, 1, 2, 0xAA])
#guard match result copyProg with
  | some (.error (.memoryOutOfBounds _ 6)) => true
  | _ => false
#guard match result (alloc_zeroed 0 *> ub (α := Unit) .switchNoMatch) with
  | some (.error .switchNoMatch) => true
  | _ => false
#guard (result (pure 7 : SirM Nat)).map (·.toOption) == some (some 7)

end SirTests.MemoryInterp
