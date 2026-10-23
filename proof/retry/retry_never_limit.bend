# eukhe: the proof of LAW retry_never_limit

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry

def never_limit(parked: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, text: Bool) -> {R.retryable(R.Facts{parked, True{}, status, kind, text}) == False{} : Bool}:
  match parked:
    case True{}:
      {==}
    case False{}:
      {==}

def Retry.retry_never_limit(parked, status, kind, text):
  never_limit(parked, status, kind, text)
