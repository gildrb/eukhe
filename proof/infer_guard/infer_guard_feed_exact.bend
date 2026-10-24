# eukhe: the proof of LAW infer_guard_feed_exact
# The longest period checked is the spec's (gb.periods), and each
# period's test on the counters is the spec's on the chunks (gb.least).

import Base
import ../../bend/infer.bend as If
import ../../bend/infer_guard.bend as M
import ../../laws/infer_guard.bend as InferGuard
import ./base.bend as LAGuard

def gfe.of(m: Maybe<&2, Nat>, -k: Nat, -s: List<&2, Nat>, -n: Nat) -> {M.feed.of(m, k, s, n) == InferGuard.feed_spec.of(m, k, s, n) : M.Next}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      {==}

def gfe.go(+k: Nat, +s: List<&2, Nat>, +n: Nat) -> {M.feed.of(M.shortest(s, k), k, s, n) == InferGuard.feed_spec.of(InferGuard.least(s, k, InferGuard.periods_spec(k)), k, s, n) : M.Next}:
  %LAGuard.gb.periods(k) : {M.feed.of(M.shortest(s, k), k, s, n) == InferGuard.feed_spec.of(InferGuard.least(s, k, _), k, s, n) : M.Next}
  %LAGuard.gb.least(s, k, If.periods(k)) : {M.feed.of(M.shortest(s, k), k, s, n) == InferGuard.feed_spec.of(_, k, s, n) : M.Next}
  gfe.of(M.shortest(s, k), k, s, n)

def InferGuard.infer_guard_feed_exact(st, x):
  match st:
    case M.St{k, seen, n}:
      gfe.go(k, x <> seen, n)
