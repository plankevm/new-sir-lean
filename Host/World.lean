import Host.Bytes
import Host.Word
import Host.Keccak
import ITree.Effect

namespace Host

inductive CallKind
  | call (value : Word)
  | delegatecall
  | staticcall
  deriving DecidableEq, Repr

abbrev Storage := Word → Word

def Storage.set (s : Storage) (key value : Word) : Storage :=
  fun k => if k = key then value else s k

/-- The running account's storage and transient storage. -/
structure Store where
  persistent : Storage
  transient : Storage
  deriving Inhabited

/-- What the frame can read of every account, itself included, apart from storage. -/
structure Accounts where
  balance : Address → Word
  extcode : Address → ByteArray
  deriving Inhabited

def Accounts.extcodehash (w : Accounts) (a : Address) : Word := .keccak256 (w.extcode a)

structure World where
  store : Store
  accounts : Accounts
  deriving Inhabited

structure World.Unset (s : World) (a : Address) : Prop where
  persistent_unset : ∀ k, s.store.persistent k = 0
  transient_unset : ∀ k, s.store.transient k = 0
  no_extcode : s.accounts.extcode a = .empty

inductive WorldOp
  | gas
  | log (topics : Array Word) (data : ByteArray)
  | call (kind : CallKind) (gas : Word) (account : Address) (input : ByteArray) (store : Store)
  | create (value : Word) (salt : Option Word) (initcode : ByteArray) (store : Store)

def WorldOp.Resp : WorldOp → Type
  | .gas => Word
  | .log .. => Unit
  | .call .staticcall .. => Bool × BytesX32
  | .call .. => Bool × BytesX32 × World
  | .create .. => Address × BytesX32 × World

abbrev WorldE : Effect := ⟨WorldOp, WorldOp.Resp⟩

end Host
