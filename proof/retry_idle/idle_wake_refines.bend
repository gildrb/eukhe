# eukhe: the proof of LAW idle_wake_refines
# The arming sleeps the whole deadline; from a timer within the deadline,
# each event meets the stall at last + d past the deadline, else comes
# with the timer still within it (LARetryIdle.ri.drive); a silent stream
# stalls at the first fire.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LARetryIdle

def RetryIdle.idle_wake_refines(gs, d, positive):
  match gs:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_gt(d, 0n), True{}, positive) : {RetryIdle.drive.start(R.idle.wake.sel(_, Nat.sub(d, 0n)), Nil{}, d) == Some{R.idle(Nil{}, d)} : Maybe<&2, R.Idle>}
      %Equal.sym(Nat, Nat.sub(d, 0n), d, LARetryIdle.ri.sub_zero(d)) : {RetryIdle.drive(Nil{}, d, 0n, _) == Some{R.idle(Nil{}, d)} : Maybe<&2, R.Idle>}
      %Equal.sym(Bool, Nat.is_gt(d, d), False{}, LARetryIdle.ri.gt_refl(d)) : {RetryIdle.silent.fire1(d, 0n, d, R.idle.wake.sel(_, Nat.sub(d, d))) == Some{R.idle(Nil{}, d)} : Maybe<&2, R.Idle>}
      {==}
    case +g <> +rest:
      %Equal.sym(Bool, Nat.is_gt(d, 0n), True{}, positive) : {RetryIdle.drive.start(R.idle.wake.sel(_, Nat.sub(d, 0n)), g <> rest, d) == Some{R.idle(g <> rest, d)} : Maybe<&2, R.Idle>}
      %Equal.sym(Nat, Nat.sub(d, 0n), d, LARetryIdle.ri.sub_zero(d)) : {RetryIdle.drive(g <> rest, d, 0n, _) == Some{R.idle(g <> rest, d)} : Maybe<&2, R.Idle>}
      LARetryIdle.ri.drive(rest, g, d, 0n, d, LARetryIdle.ri.gt_refl(d))
