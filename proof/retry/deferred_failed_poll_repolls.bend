# eukhe: the proof of LAW deferred_failed_poll_repolls
# The two premises pass the repoll test, which polls with one more failure
# in a row.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred
import ../base/bool.bend as LBool
import ../base/logic/logic.bend as LLogicLogic

def pr.again(again: Bool, +failed: Nat, +left: Nat, +gap: Nat, e: {again == True{} : Bool}) -> {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.failed(again, failed, left, gap))) == True{} : Bool} & {RetryDeferred.rs.failed(R.live.failed(again, failed, left, gap)) == 1n+failed : Nat}:
  match again:
    case True{}:
      ({==}, {==})
    case False{}:
      LLogicLogic.rp.absurdF({RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.live.failed(False{}, failed, left, gap))) == True{} : Bool} & {RetryDeferred.rs.failed(R.live.failed(False{}, failed, left, gap)) == 1n+failed : Nat}, e)

def repolls(+fails: Nat, +budget: Nat, +failed: Nat, +left: Nat, +gap: Nat, below: {Nat.is_lt(failed, fails) == True{} : Bool}, live: {Nat.is_gt(left, 0n) == True{} : Bool}) -> {RetryDeferred.rs.polled(RetryDeferred.rs.step.act(R.step(fails, budget, R.Live{failed, left}, R.Broke{True{}, gap}))) == True{} : Bool} & {RetryDeferred.rs.failed(R.step(fails, budget, R.Live{failed, left}, R.Broke{True{}, gap})) == 1n+failed : Nat}:
  pr.again(Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n)), failed, left, gap, LBool.rp.and_tt(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n), below, live))

def RetryDeferred.deferred_failed_poll_repolls(fails, budget, failed, left, gap, below, live):
  repolls(fails, budget, failed, left, gap, below, live)
