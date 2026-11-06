import Sir.Syntax
import Sir.Passes.DeadCode

namespace SirTests.DeadCode

open Sir

deriving instance DecidableEq for Expr, Stmt, Operation, Control, Block, ReturnKind, Function,
  Program

example : (sir! {
  fn init:
    entry { stop }
  fn dead:
    entry { invalid }
  fn main:
    entry { stop }
}).removeDeadCode = sir! {
  fn init:
    entry { stop }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      x = caller
      => @exit
    }
    orphan { invalid }
    exit { sstore 0 x; stop }
  fn main:
    entry { stop }
}).removeDeadCode = sir! {
  fn init:
    entry {
      x = caller
      => @exit
    }
    exit { sstore 0 x; stop }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry { stop }
    orphan { icall_never @helper }
  fn main:
    entry { stop }
  fn helper:
    entry { invalid }
}).removeDeadCode = sir! {
  fn init:
    entry { stop }
  fn main:
    entry { stop }
} := by decide +kernel

example : (sir! {
  fn init:
    entry {
      r = icall @callee 1
      sstore 0 r
      stop
    }
  fn unused:
    entry { => @0 }
  fn main:
    entry { icall_never @spin }
  fn callee -> 1:
    entry x -> x { iret }
  fn spin:
    entry { => @loop }
    dead { invalid }
    loop { => @loop }
}).removeDeadCode = sir! {
  fn init:
    entry {
      r = icall @callee 1
      sstore 0 r
      stop
    }
  fn main:
    entry { icall_never @spin }
  fn callee -> 1:
    entry x -> x { iret }
  fn spin:
    entry { => @loop }
    loop { => @loop }
} := by decide +kernel

end SirTests.DeadCode
