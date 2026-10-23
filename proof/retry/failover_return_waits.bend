# eukhe: the proof of LAW failover_return_waits

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base.bend as L

def rp.return_waits_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: L.rp.Good(m, len, ts, p)) -> {R.Switch.return_waits(m, ts) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  (rw, tail) = more
  rw

def return_waits(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.return_waits(R.next(len, ts, p), ts) == True{} : Bool}:
  rp.return_waits_of(R.next(len, ts, p), len, ts, p, L.good(len, ts, p))

def Retry.failover_return_waits(len, ts, p):
  return_waits(len, ts, p)
