# eukhe: the proof of LAW failover_never_twice_in_a_row

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base.bend as L

def rp.not_last_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: L.rp.Good(m, len, ts, p)) -> {R.Switch.not_last(m, ts) == True{} : Bool}:
  (nl, rest) = g
  nl

def never_twice_in_a_row(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.not_last(R.next(len, ts, p), ts) == True{} : Bool}:
  rp.not_last_of(R.next(len, ts, p), len, ts, p, L.good(len, ts, p))

def Retry.failover_never_twice_in_a_row(len, ts, p):
  never_twice_in_a_row(len, ts, p)
