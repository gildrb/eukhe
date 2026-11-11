# eukhe: the proof of LAW deferred_fresh_failure
# By cases on whether the classifier retries the failure.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry/deferred.bend as RetryDeferred

def RetryDeferred.deferred_fresh_failure(fails, budget, r, gap):
  match r:
    case True{}:
      ({==}, ({==}, {==}))
    case False{}:
      ({==}, ({==}, {==}))
