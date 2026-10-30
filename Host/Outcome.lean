import Host.World
import ITree.Same

inductive Host.Outcome : Type
  | ret (data : ByteArray) (store : Store)
  | revert (data : ByteArray)
  | invalid
  | selfdestruct (beneficiary : Address) (store : Store)
