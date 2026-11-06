import Sir.Syntax
import Sir.Passes.RemoveNoops

namespace SirTests.RemoveNoops

open Sir

deriving instance DecidableEq for Expr, Stmt, Operation, Control, Block, ReturnKind, Function,
  Program

example : (sir! {
  fn init:
    entry { noop; noop; stop }
  fn main:
    entry { stop }
}).removeNoops = sir! {
  fn init:
    entry { stop }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      noop
      x = caller
      noop
      sstore 0 x
      noop
      stop
    }
  fn main:
    entry { stop }
}).removeNoops = sir! {
  fn init:
    entry {
      x = caller
      sstore 0 x
      stop
    }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      x = caller
      sstore 0 x
      => @exit
    }
    exit { stop }
  fn main:
    entry { stop }
}).removeNoops = sir! {
  fn init:
    entry {
      x = caller
      sstore 0 x
      => @exit
    }
    exit { stop }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      noop
      r = icall @callee 1
      sstore 0 r
      stop
    }
  fn main:
    entry { noop; => @next }
    next { noop; invalid }
  fn callee -> 1:
    entry x -> x { noop; iret }
}).removeNoops = sir! {
  fn init:
    entry {
      r = icall @callee 1
      sstore 0 r
      stop
    }
  fn main:
    entry { => @next }
    next { invalid }
  fn callee -> 1:
    entry x -> x { iret }
} := by decide +kernel

end SirTests.RemoveNoops
