import ITree
import Host.Word
import Host.NatRange
import Host.World
import Host.Outcome

open CoFree

namespace Host

inductive ExecutionModeKind : Type | creation | call

inductive ExecutionMode : Type
  | creation (constructorData : ByteArray)
  | call (static : Bool) (calldata : ByteArray)

def ExecutionMode.kind : ExecutionMode → ExecutionModeKind
  | creation _ => .creation
  | call _ _ => .call
  

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
  mode : ExecutionMode

def Env.static (e : Env) : Bool := match e.mode with
  | .creation _ => false
  | .call static _ => static

def Env.calldata (e : Env) : ByteArray := match e.mode with
  | .creation _ => ⟨#[]⟩
  | .call _ cd => cd

inductive HostOp
  | gas
  | selfbalance
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
  | halt (outcome : Outcome)

def HostOp.Resp : HostOp → Type
  | .gas | .selfbalance | .balance _ | .extcodehash _ => Word
  | .extcode _ => ByteArray
  | .sload _ | .tload _ => Word
  | .sstore .. | .tstore .. => Unit
  | .log .. => Unit
  | .call .. => Bool × ByteArray
  | .create .. => Address × ByteArray
  | .halt _ => Empty


abbrev HostE : Effect := ⟨HostOp, HostOp.Resp⟩

variable {N : NonDeterminism}

def host (op: HostE.Op) : CoFree HostE N (HostE.Resp op)
  := CoFree.perform (E := HostE) op

def gas := host (N := N) .gas
def selfbalance := host (N := N) .selfbalance
def balance (a : Address) := host (N := N) <| .balance a
def extcodehash (a : Address) := host (N := N) <| .extcodehash a
def extcode (a : Address) := host (N := N) <| .extcode a

def sload (k : Word) := host (N := N) <| .sload k
def tload (k : Word) := host (N := N) <| .tload k
def sstore (k v : Word) := host (N := N) <| .sstore k v
def tstore (k v : Word) := host (N := N) <| .tstore k v

def log0 (data : ByteArray) := host (N := N) <| .log #[] data
def log1 (data : ByteArray) (t₀ : Word) := host (N := N) <| .log #[t₀] data
def log2 (data : ByteArray) (t₀ t₁ : Word) := host (N := N) <| .log #[t₀, t₁] data
def log3 (data : ByteArray) (t₀ t₁ t₂ : Word) := host (N := N) <| .log #[t₀, t₁, t₂] data
def log4 (data : ByteArray) (t₀ t₁ t₂ t₃ : Word) := host (N := N) <| .log #[t₀, t₁, t₂, t₃] data

def call (gas : Word) (a : Address) (value : Word) (input : ByteArray) :=
  host (N := N) <| .call (.call value) gas a input
def staticcall (gas : Word) (a : Address) (input : ByteArray) :=
  host (N := N) <| .call .staticcall gas a input
def delegatecall (gas : Word) (a : Address) (input : ByteArray) :=
  host (N := N) <| .call .delegatecall gas a input
def callcode (gas : Word) (a : Address) (value : Word) (input : ByteArray) :=
  host (N := N) <| .call (.callcode value) gas a input

def create (value : Word) (code : ByteArray) :=
  host (N := N) <| .create value none code
def create2 (value salt : Word) (code : ByteArray) :=
  host (N := N) <| .create value (some salt) code

def halt (outcome : Outcome) := host (N := N) <| .halt outcome

end Host
