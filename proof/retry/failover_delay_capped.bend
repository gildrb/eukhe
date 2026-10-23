# eukhe: the proof of LAW failover_delay_capped

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base.bend as L

def rp.capped_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: L.rp.Good(m, len, ts, p)) -> {R.Switch.capped(m, R.Policy.max(p)) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  (rw, tail) = more
  (cap, wi) = tail
  cap

def delay_capped(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.capped(R.next(len, ts, p), R.Policy.max(p)) == True{} : Bool}:
  rp.capped_of(R.next(len, ts, p), len, ts, p, L.good(len, ts, p))

def Retry.failover_delay_capped(len, ts, p):
  delay_capped(len, ts, p)
