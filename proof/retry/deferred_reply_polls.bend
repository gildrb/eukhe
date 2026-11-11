# eukhe: the proof of LAW deferred_reply_polls
# With ms left (positive) the deadline test of a deferred reply fails, so
# it polls a job with no failures in a row: by cases on the job and the ms.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred
import ../base/logic/logic.bend as LLogicLogic

def pp.pending(left: Nat, +gap: Nat, some: {Nat.is_gt(left, 0n) == True{} : Bool}) -> {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.pending(Nat.is_eq(left, 0n), left, gap))) == True{} : Bool} & {RetryDeferred.rs.failed(R.live.pending(Nat.is_eq(left, 0n), left, gap)) == 0n : Nat}:
  match left:
    case 0n:
      LLogicLogic.rp.absurdF({RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.pending(Nat.is_eq(0n, 0n), 0n, gap))) == True{} : Bool} & {RetryDeferred.rs.failed(R.live.pending(Nat.is_eq(0n, 0n), 0n, gap)) == 0n : Nat}, some)
    case 1n+k:
      ({==}, {==})

def reply_polls(+fails: Nat, +budget: Nat, job: R.Job, +gap: Nat, some: {Nat.is_gt(RetryDeferred.rs.time(budget, job), 0n) == True{} : Bool}) -> {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.step(fails, budget, job, R.Later{gap}))) == True{} : Bool} & {RetryDeferred.rs.failed(R.step(fails, budget, job, R.Later{gap})) == 0n : Nat}:
  match job:
    case R.NoJob{}:
      pp.pending(budget, gap, some)
    case R.Live{failed, +left}:
      pp.pending(left, gap, some)

def RetryDeferred.deferred_reply_polls(fails, budget, job, gap, some):
  reply_polls(fails, budget, job, gap, some)
