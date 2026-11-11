# eukhe: the proof of LAW retry_classifier_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry

# (R1) The classifier, exactly
# ----------------------------

def rx.status_go(c: Cmp, +s: Nat) -> {R.status.ok.go(Cmp.is_lt(c), s) == Bool.or(Cmp.is_ge(c), R.status.listed(s)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def rx.kind(k: R.Cause, text: Bool) -> {R.by_class(R.Cause.class(k), text) == Retry.rs.by_kind(Retry.rs.kind(k), text) : Bool}:
  match k:
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
    case R.Unknown{}:
      {==}

def rx.recorded(status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, text: Bool) -> {R.by_status(status, kind, text) == Retry.rs.recorded(status, kind, text) : Bool}:
  match status kind:
    case Some{+s} k:
      rx.status_go(Nat.cmp(s, 500n), s)
    case None{} Some{k}:
      rx.kind(k, text)
    case None{} None{}:
      {==}

def classifier_exact(f: R.Facts) -> {R.retryable(f) == Retry.rs.retryable(f) : Bool}:
  match f:
    case R.Facts{parked, limit, status, kind, text}:
      match parked limit:
        case True{} l:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          rx.recorded(status, kind, text)

def Retry.retry_classifier_exact(f):
  classifier_exact(f)
