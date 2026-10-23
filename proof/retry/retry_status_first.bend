# eukhe: the proof of LAW retry_status_first

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry

def status_first(parked: Bool, limit: Bool, +s: Nat, k1: Maybe<&2, R.Cause>, t1: Bool, k2: Maybe<&2, R.Cause>, t2: Bool) -> {R.retryable(R.Facts{parked, limit, Some{s}, k1, t1}) == R.retryable(R.Facts{parked, limit, Some{s}, k2, t2}) : Bool}:
  match parked limit:
    case True{} l:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Retry.retry_status_first(parked, limit, s, k1, t1, k2, t2):
  status_first(parked, limit, s, k1, t1, k2, t2)
