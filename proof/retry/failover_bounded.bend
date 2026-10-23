# eukhe: the proof of LAW failover_bounded

import Base
import ../../bend/retry.bend as R
import ../../LAWS.bend as Laws
import ../base.bend as L

def rp.within_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: L.rp.Good(m, len, ts, p)) -> {R.Switch.within(m, ts, p) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  (rw, tail) = more
  (cap, wi) = tail
  wi

def bounded(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.within(R.next(len, ts, p), ts, p) == True{} : Bool}:
  rp.within_of(R.next(len, ts, p), len, ts, p, L.good(len, ts, p))

def Laws.failover_bounded(len, ts, p):
  bounded(len, ts, p)
