import Host.Effect

/-! Concrete storage and world.

`interpStore` answers the frame's storage, transient storage and world reads from a `State`, and
emits `WorldE`: what is left, gas, logs, calls, creations and the end of the frame. Within a
frame only the frame itself changes its storage, and nothing changes the world, except a call or
a creation: the callee (or the initcode) may change balances and code, and may reenter and write
this account's storage. So a call or creation passes the current `Store` out (a reentrant callee
reads it) and is answered with the whole `State` afterwards, which the environment picks; `Same`
relates two runs only if they agree for every such answer. A `staticcall` changes nothing and
is answered without a `State`.

`WorldE` is where runs of different IRs are related, so it has one way to say each observable
thing: `stop` is `ret` with no data. The frame's `Store` leaves it at `ret` and `selfdestruct`;
`revert`, `invalid` and `ub` discard it. A static frame that tries to change state halts like `invalid` (EIP-214,
EIP-1153), and its callees run static too, so no call changes its state. -/

namespace Host

abbrev Storage := Word → Word

def Storage.set (s : Storage) (key value : Word) : Storage :=
  fun k => if k = key then value else s k

/-- The running account's storage and transient storage. -/
structure Store where
  storage : Storage
  transient : Storage
  deriving Inhabited

/-- What the frame can read of every account, itself included, apart from storage. -/
structure World where
  balance : Address → Word
  extcodehash : Address → Word
  extcode : Address → ByteArray
  deriving Inhabited

structure State where
  store : Store
  world : World
  deriving Inhabited

inductive WorldOp
  | gas
  | log (topics : Array Word) (data : ByteArray)
  | call (kind : CallKind) (gas : Word) (account : Address) (input : ByteArray) (store : Store)
  | create (value : Word) (salt : Option Word) (initcode : ByteArray) (store : Store)
  | ret (data : ByteArray) (store : Store)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Address) (store : Store)
  | ub (u : UB)

def WorldOp.Resp : WorldOp → Type
  | .gas => Word
  | .log .. => Unit
  | .call .staticcall .. => Bool × ByteArray
  | .call .. => Bool × ByteArray × State
  | .create .. => Address × ByteArray × State
  | .ret .. | .revert _ | .invalid | .selfdestruct .. | .ub _ => Empty

abbrev WorldE : Effect where
  Op := WorldOp
  Resp := WorldOp.Resp
  BrOp := Choice
  BrResp := Choice.Resp
  brResp_nonempty := HostE.brResp_nonempty

variable {A : Type}

def world (op : WorldOp) : CoFree WorldE (WorldOp.Resp op) := CoFree.perform (E := WorldE) op

def halt (op : WorldOp) (h : WorldOp.Resp op = Empty := by rfl) : CoFree WorldE A := do
  let e ← world op
  Empty.elim (h ▸ e)

def State.setStore (s : State) (f : Store → Store) : State := { s with store := f s.store }

def handleHost (env : Env) (s : State) : (op : HostOp) → CoFree WorldE (State × HostOp.Resp op)
  | .gas => do pure (s, ← world .gas)
  | .selfbalance => pure (s, s.world.balance env.address)
  | .balance a => pure (s, s.world.balance a)
  | .extcodehash a => pure (s, s.world.extcodehash a)
  | .extcode a => pure (s, s.world.extcode a)
  | .sload k => pure (s, s.store.storage k)
  | .tload k => pure (s, s.store.transient k)
  | .sstore k v => if env.static then halt .invalid else
    pure (s.setStore fun st => { st with storage := st.storage.set k v }, ())
  | .tstore k v => if env.static then halt .invalid else
    pure (s.setStore fun st => { st with transient := st.transient.set k v }, ())
  | .log topics data => if env.static then halt .invalid else do
    pure (s, ← world (.log topics data))
  | .call .staticcall gas account input => do
    pure (s, ← world (.call .staticcall gas account input s.store))
  | .call (.call v) gas account input => if env.static && v ≠ 0 then halt .invalid else do
    let (ok, out, s') ← world (.call (.call v) gas account input s.store)
    pure (if env.static then s else s', (ok, out))
  | .call (.callcode v) gas account input => do
    let (ok, out, s') ← world (.call (.callcode v) gas account input s.store)
    pure (if env.static then s else s', (ok, out))
  | .call .delegatecall gas account input => do
    let (ok, out, s') ← world (.call .delegatecall gas account input s.store)
    pure (if env.static then s else s', (ok, out))
  | .create value salt initcode => do
      if env.static then
        halt .invalid
      let (account, out, s') ← world (.create value salt initcode s.store)
      return (s', (account, out))
  | .stop => halt (.ret .empty s.store)
  | .ret data => halt (.ret data s.store)
  | .revert data => halt (.revert data)
  | .invalid => halt .invalid
  | .selfdestruct a => if env.static then halt .invalid else halt (.selfdestruct a s.store)
  | .ub u => halt (.ub u)

def interpStore (env : Env) (s : State) (t : CoFree HostE A) : CoFree WorldE (State × A) :=
  CoFree.interpState (E := HostE) (handleHost env) ⟨fun c => c, fun _ r => r⟩ s t

end Host
