# eukhe: the proof of LAW retry_wait_exact
# The step is the spec's (retry_step_exact); the jitter and the server's
# wait agree case by case: a step of 0 or not, no server wait, no cap or
# a positive one.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../../laws/retry_ffi.bend as RetryFfi
import ../retry/retry_step_exact.bend as PRetryStepExact

def rw.jitter(step: Nat, +draw: Nat) -> {RetryFfi.wait_spec.jitter(step, draw) == R.jitter.draw(step, draw) : Nat}:
  match step:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rw.server(refuse: Bool, +jitter: Nat, +s: Nat, +cap: Nat) -> {R.wait.server(refuse, jitter, s, cap) == RetryFfi.wait_spec.server(refuse, jitter, s, cap) : R.Delay}:
  match refuse:
    case True{}:
      {==}
    case False{}:
      {==}

def rw.of(+jitter: Nat, server: Maybe<&2, Nat>, cap: Nat) -> {R.wait(jitter, server, cap) == RetryFfi.wait_spec.of(jitter, server, cap) : R.Delay}:
  match server:
    case None{}:
      {==}
    case Some{+s}:
      match cap:
        case 0n:
          {==}
        case 1n+c:
          +C = {1n+c : Nat}
          rw.server(Nat.is_gt(s, C), jitter, s, C)

def rw.exact(+base: Nat, +attempt: Nat, +cap: Nat, +draw: Nat, +server: Maybe<&2, Nat>) -> {R.retry_wait(base, attempt, cap, draw, server) == RetryFfi.wait_spec(base, attempt, cap, draw, server) : R.Delay}:
  +step = Nat.min(Retry.rs.twice(Nat.sub(attempt, 1n), base), cap)
  %Equal.sym(Nat, R.jitter.step(base, attempt, cap), step, Retry.retry_step_exact(base, attempt, cap)) : {R.wait(R.jitter.draw(_, draw), server, cap) == RetryFfi.wait_spec(base, attempt, cap, draw, server) : R.Delay}
  %rw.jitter(step, draw) : {R.wait(_, server, cap) == RetryFfi.wait_spec(base, attempt, cap, draw, server) : R.Delay}
  rw.of(RetryFfi.wait_spec.jitter(step, draw), server, cap)

def RetryFfi.retry_wait_exact(base, attempt, cap, draw, server):
  rw.exact(base, attempt, cap, draw, server)
