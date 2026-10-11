import ITree.Machine

universe u v

namespace CoFree

variable {E : Effect.{u}} {A : Type u}

/-- Runs at most `fuel` steps, answering operations with `handle`. `none` means the fuel ran out. -/
def runM {m : Type u → Type v} [Monad m] (handle : (op : E.Op) → m (E.Resp op)) :
    Nat → CoFree E A → m (Option A)
  | 0, _ => Pure.pure none
  | fuel + 1, t => match t.observe with
    | .pure a => Pure.pure (some a)
    | .silent t => runM handle fuel t
    | .impure op k => do runM handle fuel (k (← handle op))

/-- Runs at most `fuel` steps, answering operations with `answer`. -/
def run (answer : (op : E.Op) → E.Resp op) : Nat → CoFree E A → Option A
  | 0, _ => none
  | fuel + 1, t => match t.observe with
    | .pure a => some a
    | .silent t => run answer fuel t
    | .impure op k => run answer fuel (k (answer op))

inductive Event (E : Effect.{u}) : Type u
  | silent
  | op (op : E.Op)

/-- Like `run`, also recording every silent step and operation. -/
def trace (answer : (op : E.Op) → E.Resp op) (fuel : Nat) (t : CoFree E A) :
    Array (Event E) × Option A :=
  go fuel t #[]
where
  go : Nat → CoFree E A → Array (Event E) → Array (Event E) × Option A
    | 0, _, events => (events, none)
    | fuel + 1, t, events => match t.observe with
      | .pure a => (events, some a)
      | .silent t => go fuel t (events.push .silent)
      | .impure op k => go fuel (k (answer op)) (events.push (.op op))

end CoFree
