# eukhe: the proof of LAW retry_kind_before_text

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/bool/misc.bend as LBoolMisc

def rp.known(k: R.Cause, known: {R.Cause.known(k) == True{} : Bool}, t1: Bool, t2: Bool) -> {R.by_class(R.Cause.class(k), t1) == R.by_class(R.Cause.class(k), t2) : Bool}:
  match k:
    case R.Unknown{}:
      LBoolMisc.rp.absurdF({t1 == t2 : Bool}, known)
    case R.Refusal{}:
      {==}
    case R.Safety{}:
      {==}
    case R.PaymentRequired{}:
      {==}
    case R.Overloaded{}:
      {==}
    case R.RateLimit{}:
      {==}
    case R.ServerError{}:
      {==}
    case R.Auth{}:
      {==}
    case R.Permission{}:
      {==}
    case R.InvalidRequest{}:
      {==}
    case R.MalformedResponse{}:
      {==}
    case R.StreamDrop{}:
      {==}
    case R.StreamStalled{}:
      {==}
    case R.StreamRepeating{}:
      {==}

def kind_before_text(parked: Bool, limit: Bool, k: R.Cause, known: {R.Cause.known(k) == True{} : Bool}, t1: Bool, t2: Bool) -> {R.retryable(R.Facts{parked, limit, None{}, Some{k}, t1}) == R.retryable(R.Facts{parked, limit, None{}, Some{k}, t2}) : Bool}:
  match parked limit:
    case True{} l:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      rp.known(k, known, t1, t2)

def Retry.retry_kind_before_text(parked, limit, k, known, t1, t2):
  kind_before_text(parked, limit, k, known, t1, t2)
