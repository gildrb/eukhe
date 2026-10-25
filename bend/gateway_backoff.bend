# gateway_backoff: how long the Signal gateway waits before it tries the
# daemon again (Rust: crates/eukhe-gateway link.rs and gateway.rs, at every
# failed reconnect). The first wait is 250 ms; each next one doubles the
# last, up to 10 s. Pure: no IO, no @unsafe.

import Base

# the first wait, in ms
def first() -> Nat:
  250n

# the longest wait, in ms
def most() -> Nat:
  10000n

def next.cap(b: Bool, x: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      most()

# the wait after `last` (none: the first wait), in ms
def next(last: Maybe<&2, Nat>) -> Nat:
  match last:
    case None{}:
      first()
    case Some{d}:
      +x = Nat.mul(2n, d)
      next.cap(Nat.is_le(x, most()), x)
