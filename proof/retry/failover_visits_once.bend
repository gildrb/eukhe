# eukhe: the proof of LAW failover_visits_once

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/maybe.bend as LMaybe
import ../base/retry.bend as LRetry

def rp.fresh_first_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: LMaybe.rp.Good(m, len, ts, p)) -> {R.Switch.fresh_first(m, len, ts) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  ff

def visits_once(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.fresh_first(R.next(len, ts, p), len, ts) == True{} : Bool}:
  rp.fresh_first_of(R.next(len, ts, p), len, ts, p, LRetry.good(len, ts, p))

def Retry.failover_visits_once(len, ts, p):
  visits_once(len, ts, p)
