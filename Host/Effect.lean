import Host.Word
import Host.NatRange
import Host.World
import ITree.Program

open CoFree

namespace Host

inductive ExecutionModeKind : Type | creation | call deriving DecidableEq

inductive ExecutionMode : Type
  | creation (constructorData : ByteArray)
  | call (static : Bool) (calldata : BytesX32)

def ExecutionMode.kind : ExecutionMode → ExecutionModeKind
  | creation _ => .creation
  | call _ _ => .call
  
def ExecutionMode.static : ExecutionMode → Bool
  | .creation _ => false
  | .call static _ => static

def ExecutionMode.calldata : ExecutionMode → ByteArray
  | .creation _ => .empty
  | .call _ cd => cd.val

/-- The frame's constants: the transaction, the block, the code being run, and whether the frame
may change state. -/
structure Env where
  address : Address
  origin : Address
  caller : Address
  callvalue : Word
  gasprice : Word
  chainid : Word
  coinbase : Address
  timestamp : Word
  number : Word
  prevrandao : Word
  gaslimit : Word
  basefee : Word
  blobbasefee : Word
  blockhash : Word → Word
  blobhash : Word → Word


inductive SimplifiedOutcome : Type
  | ret (data : ByteArray)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Address)

inductive HostOp
  | gas
  | selfbalance
  | returndata
  | balance (account : Address)
  | extcode (account : Address)
  | extcodehash (account : Address)
  | sload (key : Word)
  | tload (key : Word)
  | sstore (key value : Word)
  | tstore (key value : Word)
  | log (topics : Array Word) (data : ByteArray)
  | call (kind : CallKind) (gas : Word) (account : Address) (input : ByteArray)
  | create (value : Word) (salt : Option Word) (initcode : ByteArray)
  | halt (outcome : SimplifiedOutcome)


def HostOp.Resp : HostOp → Type
  | .gas | .selfbalance => Word
  | .returndata => BytesX32
  | .balance _ | .extcodehash _ => Word
  | .extcode _ => ByteArray
  | .sload _ | .tload _ => Word
  | .sstore .. | .tstore .. => Unit
  | .log .. => Unit
  | .call .. => Bool
  | .create .. => Address
  | .halt _ => Empty


abbrev HostE : Effect := ⟨HostOp, HostOp.Resp⟩
abbrev HostM (α : Type) := CoFree HostE .none α

def host (op: HostE.Op) : HostM (HostE.Resp op) := CoFree.perform op

def gas := host .gas
def selfbalance := host .selfbalance
def returndata := host .returndata
def balance (a : Address) := host <| .balance a
def extcodehash (a : Address) := host <| .extcodehash a
def extcode (a : Address) := host <| .extcode a

def persistent.load (k : Word) := host <| .sload k
def transient.load (k : Word) := host <| .tload k
def persistent.store (k v : Word) := host <| .sstore k v
def transient.store (k v : Word) := host <| .tstore k v

def log (data : ByteArray) (topics : Array Word) := host <| .log topics data

def call (gas : Word) (a : Address) (value : Word) (input : ByteArray) := host <| .call (.call value) gas a input
def staticcall (gas : Word) (a : Address) (input : ByteArray) := host <| .call .staticcall gas a input
def delegatecall (gas : Word) (a : Address) (input : ByteArray) := host <| .call .delegatecall gas a input

def create (value : Word) (code : ByteArray) := host <| .create value none code
def create2 (value salt : Word) (code : ByteArray) := host <| .create value (some salt) code

def halt {α : Type} (outcome : SimplifiedOutcome) : HostM α := do nomatch ← host <| .halt outcome

end Host
