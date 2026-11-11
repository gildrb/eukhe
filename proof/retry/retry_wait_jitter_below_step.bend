# eukhe: the proof of LAW retry_wait_jitter_below_step
# The model's step is R2's (LA.rx.wait_of); under a positive step the
# remainder of a draw is below it (LA.rx.jit_below).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base.bend as LA

def below_step(+base: Nat, +attempt: Nat, +cap: Nat, +draw: Nat, positive: {Nat.is_gt(Retry.rs.step(base, attempt, cap), 0n) == True{} : Bool}) -> {Retry.rs.before(R.retry_wait(base, attempt, cap, draw, None{}), Retry.rs.step(base, attempt, cap)) == True{} : Bool}:
  +S = Retry.rs.step(base, attempt, cap)
  %Equal.sym(R.Delay, R.retry_wait(base, attempt, cap, draw, None{}), R.After{R.jitter.draw(S, draw)}, LA.rx.wait_of(base, attempt, cap, draw)) : {Retry.rs.before(_, S) == True{} : Bool}
  LA.rx.jit_below(S, draw, positive)

def Retry.retry_wait_jitter_below_step(base, attempt, cap, draw, positive):
  below_step(base, attempt, cap, draw, positive)
