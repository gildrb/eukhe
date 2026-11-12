# eukhe: the proof of LAW deferred_deadline_cancels
# With no ms left (0) the deadline test of a deferred reply passes, so it
# cancels: by cases on the job, rewriting its ms to 0.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred

def deadline(+fails: Nat, +budget: Nat, job: R.Job, +gap: Nat, none: {RetryDeferred.rs.time(budget, job) == 0n : Nat}) -> {R.step(fails, budget, job, R.Later{gap}) == R.Step{R.Cancel{}, R.NoJob{}} : R.Step}:
  match job:
    case R.NoJob{}:
      %Equal.sym(Nat, budget, 0n, none) : {R.live.pending(Nat.is_eq(_, 0n), _, gap) == R.Step{R.Cancel{}, R.NoJob{}} : R.Step}
      {==}
    case R.Live{failed, +left}:
      %Equal.sym(Nat, left, 0n, none) : {R.live.pending(Nat.is_eq(_, 0n), _, gap) == R.Step{R.Cancel{}, R.NoJob{}} : R.Step}
      {==}

def RetryDeferred.deferred_deadline_cancels(fails, budget, job, gap, none):
  deadline(fails, budget, job, gap, none)
