# eukhe: the proof of LAW deferred_answer_settles
# By cases on the job: both arms of an answer settle.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred

def RetryDeferred.deferred_answer_settles(fails, budget, job):
  match job:
    case R.NoJob{}:
      {==}
    case R.Live{failed, left}:
      {==}
