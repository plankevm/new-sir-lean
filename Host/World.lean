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
  storage : Storage
  transient : Storage
  deriving Inhabited

/-- What the frame can read of every account, itself included, apart from storage. -/
structure Accounts where
  balance : Address → Word
  extcode : Address → ByteArray
  deriving Inhabited

def Accounts.extcodehash (w : Accounts) (a : Address) : Word := .keccak256 (w.extcode a)

structure State where
  store : Store
  accounts : Accounts
  deriving Inhabited

inductive WorldOp
  | gas
  | log (topics : Array Word) (data : ByteArray)
  | call (kind : CallKind) (gas : Word) (account : Address) (input : ByteArray) (store : Store)
  | create (value : Word) (salt : Option Word) (initcode : ByteArray) (store : Store)

def WorldOp.Resp : WorldOp → Type
  | .gas => Word
  | .log .. => Unit
  | .call .staticcall .. => Bool × ByteArray
  | .call .. => Bool × ByteArray × State
  | .create .. => Address × ByteArray × State

abbrev WorldE : Effect := ⟨WorldOp, WorldOp.Resp⟩

end Host
