# infer_force: a forced tool call one attempt at a time (bend/infer.bend
# section 2, `force`, as the harness drives it: crates/eukhe-durable
# generation.rs asks for each request's native flag, then reads its reply).
# Attempts count from 0 (the first request). laws/infer_force.bend pins
# both steps (`flag`, `after`) and that, driven over the replies, they are
# `force`; bend/ffi_infer_force.bend runs them as the compiled core.

import Base
import ./infer.bend as If

# what follows the reply to an attempt
type Next is Data:
  Hit{}    # the model called the tool: the reply goes on as any other
  Again{}  # no call, and a retry remains: the next attempt goes
  Fails{}  # no call on the last attempt: the forced call fails

# the native flag of attempt i: on the first only when the provider
# supports it and it is free, on every retry when the provider supports it
def flag(i: Nat, sup: Bool, free: Bool) -> Bool:
  match i:
    case 0n:
      Bool.and(sup, free)
    case 1n+j:
      sup

def after.miss(more: Bool) -> Next:
  match more:
    case True{}:
      Again{}
    case False{}:
      Fails{}

# the step after the reply to attempt i of a call with r retries: c says
# the model called the tool; a miss retries while i < r
def after(i: Nat, r: Nat, c: Bool) -> Next:
  match c:
    case True{}:
      Hit{}
    case False{}:
      after.miss(Nat.is_lt(i, r))
