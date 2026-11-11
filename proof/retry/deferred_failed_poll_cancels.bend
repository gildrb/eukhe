# eukhe: the proof of LAW deferred_failed_poll_cancels
# The repoll test (retryable, below retry.maxRetries, time left) fails
# when the failure is not retryable, the failures reached the limit
# (fails <= failed, so not failed < fails) or no ms is left (left = 0, so
# not left > 0); a failed repoll test cancels.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# a <= b gives not b < a
def pf.le_not_lt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.rp.absurdF({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      pf.le_not_lt(p, q, h)

# left = 0 gives not left > 0
def pf.zero_not_gt(left: Nat, h: {Nat.is_eq(left, 0n) == True{} : Bool}) -> {Nat.is_gt(left, 0n) == False{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+k:
      LLogicLogic.rp.absurdF({Nat.is_gt(1n+k, 0n) == False{} : Bool}, h)

# the limit reached, or no ms left: the last two conjuncts of the test fail
def pf.or_case(c: Bool, +fails: Nat, +failed: Nat, +left: Nat, ec: {Nat.is_le(fails, failed) == c : Bool}, h: {Bool.or(c, Nat.is_eq(left, 0n)) == True{} : Bool}) -> {Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n)) == False{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(failed, fails), False{}, pf.le_not_lt(fails, failed, ec)) : {Bool.and(_, Nat.is_gt(left, 0n)) == False{} : Bool}
      {==}
    case False{}:
      LA.rx.and_f(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n), pf.zero_not_gt(left, h))

def pf.cancel(again: Bool, +failed: Nat, +left: Nat, +gap: Nat, e: {again == False{} : Bool}) -> {R.live.failed(again, failed, left, gap) == R.Step{R.Cancel{}, R.NoJob{}} : R.Step}:
  match again:
    case True{}:
      LLogicLogic.rp.absurdT({R.live.failed(True{}, failed, left, gap) == R.Step{R.Cancel{}, R.NoJob{}} : R.Step}, e)
    case False{}:
      {==}

def cancels(+fails: Nat, +budget: Nat, +failed: Nat, +left: Nat, r: Bool, +gap: Nat, stop: {Bool.or(Bool.not(r), Bool.or(Nat.is_le(fails, failed), Nat.is_eq(left, 0n))) == True{} : Bool}) -> {R.step(fails, budget, R.Live{failed, left}, R.Broke{r, gap}) == R.Step{R.Cancel{}, R.NoJob{}} : R.Step}:
  match r:
    case True{}:
      pf.cancel(Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n)), failed, left, gap, pf.or_case(Nat.is_le(fails, failed), fails, failed, left, {==}, stop))
    case False{}:
      {==}

def RetryDeferred.deferred_failed_poll_cancels(fails, budget, failed, left, r, gap, stop):
  cancels(fails, budget, failed, left, r, gap, stop)
