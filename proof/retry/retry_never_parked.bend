# eukhe: the proof of LAW retry_never_parked

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry

# (R1) The classifier
# -------------------

def never_parked(limit: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, text: Bool) -> {R.retryable(R.Facts{True{}, limit, status, kind, text}) == False{} : Bool}:
  {==}

# (R) Retries

def Retry.retry_never_parked(limit, status, kind, text):
  never_parked(limit, status, kind, text)
