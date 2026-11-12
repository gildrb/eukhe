# eukhe: the proof of LAW deferred_poll_charged
# Every poll the step makes leaves Live{_, left - (1 + gap)} for the left
# (or budget) it read: by cases on the job, the reply and the tests.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred
import ../base/nat.bend as LNat

def pc.pending(over: Bool, +left: Nat, +gap: Nat) -> {RetryDeferred.rs.charged(R.live.pending(over, left, gap), left, gap) == True{} : Bool}:
  match over:
    case True{}:
      {==}
    case False{}:
      LNat.child.pc.eq_refl(Nat.sub(left, 1n+gap))

def pc.failed(again: Bool, +failed: Nat, +left: Nat, +gap: Nat) -> {RetryDeferred.rs.charged(R.live.failed(again, failed, left, gap), left, gap) == True{} : Bool}:
  match again:
    case True{}:
      LNat.child.pc.eq_refl(Nat.sub(left, 1n+gap))
    case False{}:
      {==}

def charged(+fails: Nat, +budget: Nat, job: R.Job, g: R.Got) -> {RetryDeferred.rs.charged(R.step(fails, budget, job, g), RetryDeferred.rs.time(budget, job), RetryDeferred.rs.gap(g)) == True{} : Bool}:
  match job:
    case R.NoJob{}:
      match g:
        case R.Answer{}:
          {==}
        case R.Later{+gap}:
          pc.pending(Nat.is_eq(budget, 0n), budget, gap)
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
          pc.pending(Nat.is_eq(left, 0n), left, gap)
        case R.Broke{r, +gap}:
          pc.failed(Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))), failed, left, gap)

def RetryDeferred.deferred_poll_charged(fails, budget, job, g):
  charged(fails, budget, job, g)
