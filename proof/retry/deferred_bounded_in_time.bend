# eukhe: the proof of LAW deferred_bounded_in_time
# With no ms left (0 as the job's left, or as a new job's budget) the
# deadline test of a deferred reply cancels, and the repoll test of a
# failed poll fails (its time-left conjunct is false): by cases on the job
# and the reply.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# a failed poll whose repoll test fails is no poll
def pb.failed(again: Bool, +failed: Nat, +left: Nat, +gap: Nat, e: {again == False{} : Bool}) -> {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.failed(again, failed, left, gap))) == False{} : Bool}:
  match again:
    case True{}:
      LLogicLogic.rp.absurdT({RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.failed(True{}, failed, left, gap))) == False{} : Bool}, e)
    case False{}:
      {==}

def bounded(+fails: Nat, +budget: Nat, job: R.Job, g: R.Got, none: {RetryDeferred.rs.time(budget, job) == 0n : Nat}) -> {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.step(fails, budget, job, g))) == False{} : Bool}:
  match job:
    case R.NoJob{}:
      match g:
        case R.Answer{}:
          {==}
        case R.Later{+gap}:
          %Equal.sym(Nat, budget, 0n, none) : {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.pending(Nat.is_eq(_, 0n), _, gap))) == False{} : Bool}
          {==}
        case R.Broke{r, gap}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
    case R.Live{+failed, +left}:
      match g:
        case R.Answer{}:
          {==}
        case R.Later{+gap}:
          %Equal.sym(Nat, left, 0n, none) : {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.pending(Nat.is_eq(_, 0n), _, gap))) == False{} : Bool}
          {==}
        case R.Broke{+r, +gap}:
          %Equal.sym(Nat, left, 0n, none) : {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.failed(Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(_, 0n))), failed, _, gap))) == False{} : Bool}
          pb.failed(Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(0n, 0n))), failed, 0n, gap, LA.rx.and_f(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(0n, 0n)), LA.rx.and_f(Nat.is_lt(failed, fails), Nat.is_gt(0n, 0n), {==})))

def RetryDeferred.deferred_bounded_in_time(fails, budget, job, g, none):
  bounded(fails, budget, job, g, none)
