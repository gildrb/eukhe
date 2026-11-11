# eukhe: the proof of LAW retry_wait_jitter_spread
# The model's step is R2's (LA.rx.wait_of); under it a draw below the step
# is its own remainder (LA.rx.jit_small).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base.bend as LA

def spread(+base: Nat, +attempt: Nat, +cap: Nat, +j: Nat, below: {Nat.is_lt(j, Retry.rs.step(base, attempt, cap)) == True{} : Bool}) -> {R.retry_wait(base, attempt, cap, j, None{}) == R.After{j} : R.Delay}:
  +S = Retry.rs.step(base, attempt, cap)
  Equal.trans(R.Delay, R.retry_wait(base, attempt, cap, j, None{}), R.After{R.jitter.draw(S, j)}, R.After{j}, LA.rx.wait_of(base, attempt, cap, j), Equal.cong(Nat, R.Delay, x => R.After{x}, R.jitter.draw(S, j), j, LA.rx.jit_small(S, j, below)))

def Retry.retry_wait_jitter_spread(base, attempt, cap, j, below):
  spread(base, attempt, cap, j, below)
