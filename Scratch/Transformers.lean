/-!
# Monad transformers: a tiny crash course (scratch file, not part of any lib)

Run: `lake env lean Scratch/Transformers.lean`, or open in the editor and
ctrl-click any name (`ExceptT`, `StateT`, `MonadLift`, ...) to see the real defs.

Big idea: a transformer `T m` takes a monad `m` and returns a new monad that
adds one feature *on top of* `m`. They are just type-level wrappers:

    ExceptT ε m α  :=  m (Except ε α)          -- "m, but the result may be an error"
    StateT  σ m α  :=  σ → m (α × σ)           -- "m, but threading a state"
    ReaderT ρ m α  :=  ρ → m α                 -- "m, but with a read-only env"

Stacking = nesting these definitions. Nothing magic.
-/

-- 1. They really are just those types. Check the real defs:
#print ExceptT          -- def ExceptT ε m α := m (Except ε α)
#print StateT           -- def StateT σ m α := σ → m (α × σ)
#print StateM           -- abbrev StateM σ := StateT σ Id

example (ε α : Type) (m : Type → Type) : ExceptT ε m α = m (Except ε α) := rfl
example (σ α : Type) (m : Type → Type) : StateT σ m α = (σ → m (α × σ)) := rfl

/-! ## 2. Toy versions, so you can see what bind does -/
namespace Toy

def ExceptT (ε : Type) (m : Type → Type) (α : Type) := m (Except ε α)

-- bind: run the inner `m`, look at the Except, short-circuit on error.
def ExceptT.bind [Monad m] (x : ExceptT ε m α) (f : α → ExceptT ε m β) : ExceptT ε m β :=
  show m (Except ε β) from do
    match ← (x : m (Except ε α)) with
    | .error e => pure (.error e)       -- stop here, never call f
    | .ok a    => f a

def StateT (σ : Type) (m : Type → Type) (α : Type) := σ → m (α × σ)

-- bind: feed the state from x's output into f.
def StateT.bind [Monad m] (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
  fun s => do
    let (a, s') ← x s
    f a s'

-- lift: embed an inner action, adding the "boring" layer around it.
def ExceptT.lift [Monad m] (x : m α) : ExceptT ε m α := show m (Except ε α) from Except.ok <$> x
def StateT.lift  [Monad m] (x : m α) : StateT σ m α  := fun s => (·, s) <$> x

end Toy

/-! ## 3. Order matters: the two ways to combine State + Except

    StateT σ (Except ε) α  =  σ → Except ε (α × σ)     -- error DISCARDS the state
    ExceptT ε (StateM σ) α =  σ → (Except ε α × σ)     -- state SURVIVES the error

Read the outer-most constructor last: the *inner* monad is the "base" whose
effects are more fundamental. -/

-- The same program, polymorphic in the stack via the generic classes:
--   MonadStateOf σ m  gives get/set/modify
--   MonadExceptOf ε m gives throw/tryCatch
-- Both stacks have instances, found by lifting through layers automatically.
def prog [Monad m] [MonadStateOf Nat m] [MonadExceptOf String m] : m Unit := do
  modify (· + 1)          -- counter := 1
  throw "boom"            -- fail after mutating

abbrev StateOverExcept := StateT Nat (Except String)   -- σ → Except ε (α × σ)
abbrev ExceptOverState := ExceptT String (StateM Nat)  -- σ → (Except ε α × σ)

#eval (prog : StateOverExcept Unit).run 0       -- Except.error "boom"         (state gone)
#eval (prog : ExceptOverState Unit).run.run 0   -- (Except.error "boom", 1)    (state kept)

-- Same story for `try/catch`: does catching roll back the state?
def progCatch [Monad m] [MonadStateOf Nat m] [MonadExceptOf String m] : m Nat := do
  tryCatch (do modify (· + 10); throw "boom") (fun _ => pure ())
  get

#eval (progCatch : StateOverExcept Nat).run' 0      -- ok 0   : catch = rollback (transactional)
#eval (progCatch : ExceptOverState Nat).run.run' 0  -- ok 10  : mutation persisted

/-! ## 4. Lifting: how `←` reaches inner layers

`MonadLift m n` says "an `m` action can be used in `n`". Transformers provide
`MonadLift m (T m)`; `MonadLiftT` is its transitive closure, so do-notation
auto-inserts `liftM`s through any number of layers. -/

def inner : StateM Nat Nat := do modify (· * 2); get

def outer : ExceptT String (StateM Nat) Nat := do
  let n ← inner                -- auto-lifted: StateM Nat ⟶ ExceptT String (StateM Nat)
  if n > 5 then throw "too big"
  return n

#eval outer.run.run 3   -- (error "too big", 6)
#eval outer.run.run 2   -- (ok 4, 4)

-- explicit version of what `←` inserted:
example : ExceptT String (StateM Nat) Nat := liftM inner
example : ExceptT String (StateM Nat) Nat := ExceptT.lift inner

/-! ## 5. "Flipping inside out" = just running / reinterpreting layers

`.run` peels off one layer, exposing the representation:
    x            : ExceptT ε (StateM σ) α
    x.run        : StateM σ (Except ε α)
    x.run.run s  : Except ε α × σ

You can't generically swap two arbitrary transformers, but for concrete
stacks you can write a conversion when semantics allow it, e.g. the lossy one: -/

def dropStateOnError (x : ExceptT ε (StateM σ) α) : StateT σ (Except ε) α :=
  fun s => match x.run.run s with
    | (.ok a, s')   => .ok (a, s')
    | (.error e, _) => .error e     -- this direction throws info away; the other can't be built

/-! ## 6. Why this matters for the Host halt handler

Handler sketch: `ExceptT Outcome (CoFree WorldE N) α`
  = `CoFree WorldE N (Except Outcome α)`.
`throw (.invalid)` short-circuits the rest of the handler; the tree just ends
in `pure (.error .invalid)`. So halting becomes a *return value* of the tree,
not an event — and `Same R` with an `R` on `Except Outcome α` relates halts. -/
