import Sir

namespace SirTests.Safety

open Sir Host CoFree

def noop : Program := sir! {
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
}

def initStops : Program := sir! {
  fn init:
    entry { stop }
  fn main:
    entry { stop }
}

end SirTests.Safety
