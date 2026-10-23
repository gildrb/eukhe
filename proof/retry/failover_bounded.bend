# eukhe: the proof of LAW failover_bounded

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/maybe.bend as LMaybe
import ../base/retry.bend as LRetry

def rp.within_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: LMaybe.rp.Good(m, len, ts, p)) -> {R.Switch.within(m, ts, p) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  (rw, tail) = more
  (cap, wi) = tail
  wi

def bounded(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.within(R.next(len, ts, p), ts, p) == True{} : Bool}:
  rp.within_of(R.next(len, ts, p), len, ts, p, LRetry.good(len, ts, p))

def Retry.failover_bounded(len, ts, p):
  bounded(len, ts, p)
