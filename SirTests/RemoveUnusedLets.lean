import Sir.Syntax
import Sir.Passes.RemoveUnusedLets

namespace SirTests.RemoveUnusedLets

open Sir

deriving instance DecidableEq for Expr, Stmt, Operation, Control, Block, ReturnKind, Function,
  Program

example : (sir! {
  fn init:
    entry {
      $0 = calldataload 0
      $1 = mload256 $0
      $2 = sload $1
      stop
    }
  fn main:
    entry { stop }
}).removeUnusedLets = sir! {
  fn init:
    entry { stop }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      $0 = caller
      $1 = add $0 $0
      $2 = keccak256 $0 $1
      sstore $0 $0
      stop
    }
  fn main:
    entry { stop }
}).removeUnusedLets = sir! {
  fn init:
    entry {
      $0 = caller
      sstore $0 $0
      stop
    }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      $0 = gas
      $1 = calldatasize
      $2 = malloc $1
      $3 = call $1 $1 $1 $1 $1 $1 $1
      stop
    }
  fn main:
    entry { stop }
}).removeUnusedLets = sir! {
  fn init:
    entry {
      $0 = gas
      $1 = calldatasize
      $3 = call $1 $1 $1 $1 $1 $1 $1
      stop
    }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      $0 = calldatasize
      $1 = iszero $0
      $2 = not $1
      => $1 ? @yes : @no
    }
    yes { $3 = sload $0; return $0 $0 }
    no { stop }
  fn main:
    entry { stop }
}).removeUnusedLets = sir! {
  fn init:
    entry {
      $0 = calldatasize
      $1 = iszero $0
      => $1 ? @yes : @no
    }
    yes { return $0 $0 }
    no { stop }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      $0 = calldatasize
      $1 = malloc $0
      $2 = mload256 $1
      $3 = mallocany $2
      $4 = sload $3
      stop
    }
  fn main:
    entry { stop }
}).removeUnusedLets = sir! {
  fn init:
    entry { stop }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      $0 = calldatasize
      $1 = malloc $0
      $2 = mallocany 32
      mstore256 $1 $0
      stop
    }
  fn main:
    entry { stop }
}).removeUnusedLets = sir! {
  fn init:
    entry {
      $0 = calldatasize
      $1 = malloc $0
      mstore256 $1 $0
      stop
    }
  fn main:
    entry { stop }
} := by decide +kernel

end SirTests.RemoveUnusedLets
