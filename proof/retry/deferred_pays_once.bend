# eukhe: the proof of LAW deferred_pays_once
# A live job's step settles, polls or cancels: by cases on the reply, the
# deadline test and the repoll test.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred

def pd.pending(over: Bool, +left: Nat, +gap: Nat) -> {RetryDeferred.rs.sent(RetryDeferred.rs.step.act(R.live.pending(over, left, gap))) == False{} : Bool}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def pd.failed(again: Bool, +failed: Nat, +left: Nat, +gap: Nat) -> {RetryDeferred.rs.sent(RetryDeferred.rs.step.act(R.live.failed(again, failed, left, gap))) == False{} : Bool}:
  match again:
    case True{}:
      {==}
    case False{}:
      {==}

def pays_once(+fails: Nat, +budget: Nat, +failed: Nat, +left: Nat, g: R.Got) -> {RetryDeferred.rs.sent(RetryDeferred.rs.step.act(R.step(fails, budget, R.Live{failed, left}, g))) == False{} : Bool}:
  match g:
    case R.Answer{}:
      {==}
    case R.Later{+gap}:
      pd.pending(Nat.is_eq(left, 0n), left, gap)
    case R.Broke{r, +gap}:
      pd.failed(Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))), failed, left, gap)

def RetryDeferred.deferred_pays_once(fails, budget, failed, left, g):
  pays_once(fails, budget, failed, left, g)
