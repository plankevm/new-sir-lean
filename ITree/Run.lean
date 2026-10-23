import ITree.Machine

universe u v

namespace CoFree

variable {E : Effect.{u}} {A : Type u}

/-- Runs at most `fuel` steps, answering operations with `handle` and picking branches with
`pick`. `none` means the fuel ran out. -/
def runM {m : Type u → Type v} [Monad m] (handle : (op : E.Op) → m (E.Resp op))
    (pick : (c : E.BrOp) → m (E.BrResp c)) : Nat → CoFree E A → m (Option A)
  | 0, _ => Pure.pure none
  | fuel + 1, t => match t.observe with
    | .pure a => Pure.pure (some a)
    | .silent t => runM handle pick fuel t
    | .impure op k => do runM handle pick fuel (k (← handle op))
    | .br c k => do runM handle pick fuel (k (← pick c))

/-- Runs at most `fuel` steps, answering operations with `answer` and picking branches with
`pick`. -/
def run (answer : (op : E.Op) → E.Resp op) (pick : (c : E.BrOp) → E.BrResp c) :
    Nat → CoFree E A → Option A
  | 0, _ => none
  | fuel + 1, t => match t.observe with
    | .pure a => some a
    | .silent t => run answer pick fuel t
    | .impure op k => run answer pick fuel (k (answer op))
    | .br c k => run answer pick fuel (k (pick c))

inductive Event (E : Effect.{u}) : Type u
  | silent
  | op (op : E.Op)
  | br (c : E.BrOp)

/-- Like `run`, also recording every silent step, operation and branch. -/
def trace (answer : (op : E.Op) → E.Resp op) (pick : (c : E.BrOp) → E.BrResp c) (fuel : Nat)
    (t : CoFree E A) : Array (Event E) × Option A :=
  go fuel t #[]
where
  go : Nat → CoFree E A → Array (Event E) → Array (Event E) × Option A
    | 0, _, events => (events, none)
    | fuel + 1, t, events => match t.observe with
      | .pure a => (events, some a)
      | .silent t => go fuel t (events.push .silent)
      | .impure op k => go fuel (k (answer op)) (events.push (.op op))
      | .br c k => go fuel (k (pick c)) (events.push (.br c))

end CoFree
