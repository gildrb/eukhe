# eukhe: the proof of LAW retry_wait_jitter_periodic
# The model's step is R2's (LA.rx.wait_of); a draw one step later has the
# same remainder (LA.rx.jit_period).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ./base.bend as LA

def periodic(+base: Nat, +attempt: Nat, +cap: Nat, +draw: Nat) -> {R.retry_wait(base, attempt, cap, Nat.add(Retry.rs.step(base, attempt, cap), draw), None{}) == R.retry_wait(base, attempt, cap, draw, None{}) : R.Delay}:
  +S = Retry.rs.step(base, attempt, cap)
  +late = Nat.add(S, draw)
  +same = Equal.cong(Nat, R.Delay, x => R.After{x}, R.jitter.draw(S, late), R.jitter.draw(S, draw), LA.rx.jit_period(S, draw))
  Equal.trans(R.Delay, R.retry_wait(base, attempt, cap, late, None{}), R.After{R.jitter.draw(S, late)}, R.retry_wait(base, attempt, cap, draw, None{}), LA.rx.wait_of(base, attempt, cap, late), Equal.trans(R.Delay, R.After{R.jitter.draw(S, late)}, R.After{R.jitter.draw(S, draw)}, R.retry_wait(base, attempt, cap, draw, None{}), same, Equal.sym(R.Delay, R.retry_wait(base, attempt, cap, draw, None{}), R.After{R.jitter.draw(S, draw)}, LA.rx.wait_of(base, attempt, cap, draw))))

def Retry.retry_wait_jitter_periodic(base, attempt, cap, draw):
  periodic(base, attempt, cap, draw)
