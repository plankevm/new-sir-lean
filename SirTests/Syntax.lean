import Sir.Syntax

namespace SirTests.Syntax

open Sir

example : sir! {
  fn init:
    entry {
      len = runtime_length
      ptr = malloc len
      off = runtime_start_offset
      codecopy ptr off len
      return ptr len
    }
  fn main:
    entry { stop }
} = {
  init := 0, main := 1, mainDatas := [],
  functions := #[
    { entry := 0, returns := .never, blocks := #[
      { ops := #[.let 0 .mainLength, .let 1 (.malloc 0), .let 2 .mainStartOffset,
          .stmt (.codecopy 1 2 0)],
        control := .return 1 0 }] },
    { entry := 0, returns := .never, blocks := #[{ control := .stop }] }] } := rfl

example : sir! {
  fn main:
    entry { stop }
  fn init:
    entry -> i acc {
      i = const 0
      acc = const 0
      => @head
    }
    head i acc -> i acc {
      acc = add acc i
      i = add i 1
      c = lt i 10
      => c ? @head : @done
    }
    done i acc {
      sstore 0 acc
      stop
    }
} = {
  init := 1, main := 0, mainDatas := [],
  functions := #[
    { entry := 0, returns := .never, blocks := #[{ control := .stop }] },
    { entry := 0, returns := .never, blocks := #[
      { outputs := #[0, 1], ops := #[.let 0 (.const 0), .let 1 (.const 0)],
        control := .continuesTo 1 },
      { inputs := #[0, 1], outputs := #[0, 1],
        ops := #[.let 1 (.binop .add 1 0), .let 2 (.const 1), .let 0 (.binop .add 0 2),
          .let 4 (.const 10), .let 3 (.binop .lt 0 4)],
        control := .branches 3 1 2 },
      { inputs := #[0, 1], ops := #[.let 5 (.const 0), .stmt (.sstore 5 1)],
        control := .stop }] }] } := rfl

example : sir! {
  fn init:
    entry a b {
      r = icall @callee a b
      switch r { 0 => @done 7 => @done default => @fail }
    }
    done { stop }
    fail { revert 0 0 }
  fn main:
    entry x { icall_never @spin x }
  fn callee -> 1:
    entry x y -> z {
      z = sub x y
      iret
    }
  fn spin:
    entry { => @0 }
} = {
  init := 0, main := 1, mainDatas := [],
  functions := #[
    { entry := 0, returns := .never, blocks := #[
      { inputs := #[0, 1], ops := #[.icall 2 #[0, 1] #[2]],
        control := .switch 2 #[(0, 1), (7, 1)] (some 2) },
      { control := .stop },
      { ops := #[.let 3 (.const 0), .let 4 (.const 0)], control := .revert 3 4 }] },
    { entry := 0, returns := .never, blocks := #[
      { inputs := #[0], control := .icallNever 3 #[0] }] },
    { entry := 0, returns := .values 1, blocks := #[
      { inputs := #[0, 1], outputs := #[2], ops := #[.let 2 (.binop .sub 0 1)],
        control := .iret }] },
    { entry := 0, returns := .never, blocks := #[{ control := .continuesTo 0 }] }] } := rfl

example : sir! {
  data greeting 0x0048656c6c6f
  data tail 0x00
  immutable owner 20
  immutable flag 1
  fn init:
    entry {
      len = runtime_length
      ptr = mallocany len
      g = data_offset .greeting
      setimmutable %flag ptr g
      return ptr len
    }
  fn main:
    entry {
      v = getimmutable %owner
      w = mload256 v
      mstore8 w v
      h = keccak256 w 32
      log1 w 32 h
      stop
    }
} = {
  init := 0, main := 1,
  data := #[⟨#[0x00, 0x48, 0x65, 0x6c, 0x6c, 0x6f]⟩, ⟨#[0x00]⟩], mainDatas := [0, 1],
  immutables := #[⟨20, by decide⟩, ⟨1, by decide⟩],
  functions := #[
    { entry := 0, returns := .never, blocks := #[
      { ops := #[.let 0 .mainLength, .let 1 (.mallocany 0), .let 2 (.dataOffset 0),
          .stmt (.setImmutable 1 1 2)],
        control := .return 1 0 }] },
    { entry := 0, returns := .never, blocks := #[
      { ops := #[.let 0 (.getImmutable 0), .let 1 (.mload ⟨32, by decide⟩ 0),
          .stmt (.mstore ⟨1, by decide⟩ 1 0), .let 3 (.const 32), .let 2 (.keccak256 1 3),
          .let 4 (.const 32), .stmt (.log1 1 4 2)],
        control := .stop }] }] } := rfl

example : sir! {
  fn init:
    entry $0 {
      x = add $0 (2 ^ 255)
      $3 = caller
      y = difficulty
      sstore x $3; sstore $3 y
      invalid
    }
  fn main:
    entry { selfdestruct 0xB }
} = {
  init := 0, main := 1, mainDatas := [],
  functions := #[
    { entry := 0, returns := .never, blocks := #[
      { inputs := #[0], ops := #[.let 2 (.const (2 ^ 255)), .let 1 (.binop .add 0 2),
          .let 3 (.query .caller), .let 4 (.query .prevrandao), .stmt (.sstore 1 3),
          .stmt (.sstore 3 4)],
        control := .invalid }] },
    { entry := 0, returns := .never, blocks := #[
      { ops := #[.let 0 (.const 0xB)], control := .selfdestruct 0 }] }] } := rfl

end SirTests.Syntax
