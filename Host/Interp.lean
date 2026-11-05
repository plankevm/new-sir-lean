import Host.Effect

namespace Host

inductive Outcome : Type
  | ret (data : ByteArray) (store : Store)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Address) (store : Store)

structure HostState where
  world : State
  returndata : ByteArray

def HostState.store (h : HostState) : Store := h.world.store
def HostState.accounts (h : HostState) : Accounts := h.world.accounts

def HostState.setStore (h : HostState) (store : Store) : HostState :=
  { h with world := { h.world with store } }

def SimplifiedOutcome.withStore (store : Store) : SimplifiedOutcome → Outcome
  | .ret data => .ret data store
  | .revert data => .revert data
  | .invalid => .invalid
  | .selfdestruct beneficiary => .selfdestruct beneficiary store


def hostStep {N : NonDeterminism} {A X : Type} (self : Address) (h : HostState) :
    Step HostE N A X → Step WorldE N (A ⊕ Outcome) (HostState × X)
  | .pure a => .pure (.inl a)
  | .silent x => .silent (h, x)
  | .branch c k => .branch c fun r => (h, k r)
  | .impure op k => match op with
    | .gas => .impure .gas fun r => (h, k r)
    | .selfbalance => .silent (h, k (h.accounts.balance self))
    | .returndata => .silent (h, k h.returndata)
    | .balance a => .silent (h, k (h.accounts.balance a))
    | .extcode a => .silent (h, k (h.accounts.extcode a))
    | .extcodehash a => .silent (h, k (h.accounts.extcodehash a))
    | .sload key => .silent (h, k (h.store.persistent key))
    | .tload key => .silent (h, k (h.store.transient key))
    | .sstore key value =>
      .silent (h.setStore { h.store with persistent := h.store.persistent.set key value }, k ())
    | .tstore key value =>
      .silent (h.setStore { h.store with transient := h.store.transient.set key value }, k ())
    | .log topics data => .impure (.log topics data) fun r => (h, k r)
    | .call (.call value) gas a input =>
      .impure (.call (.call value) gas a input h.store) fun (ok, rd, world) =>
        ({ world, returndata := rd }, k ok)
    | .call .delegatecall gas a input =>
      .impure (.call .delegatecall gas a input h.store) fun (ok, rd, world) =>
        ({ world, returndata := rd }, k ok)
    | .call .staticcall gas a input =>
      .impure (.call .staticcall gas a input h.store) fun (ok, rd) =>
        ({ h with returndata := rd }, k ok)
    | .create value salt initcode =>
      .impure (.create value salt initcode h.store) fun (addr, rd, world) =>
        ({ world, returndata := rd }, k addr)
    | .halt outcome => .pure (.inr (outcome.withStore h.store))

def interpHost {N : NonDeterminism} {A : Type} (self : Address) (w₀ : State) :
    CoFree HostE N A → CoFree WorldE N (A ⊕ Outcome) :=
  CoFree.interp (hostStep self) ⟨w₀, .empty⟩

end Host
