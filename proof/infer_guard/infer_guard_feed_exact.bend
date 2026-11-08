# eukhe: the proof of LAW infer_guard_feed_exact
# The gate on the window's chunks changes no answer (gb.cover), the
# longest period checked is the spec's (gb.periods), and each period's
# test on the counters is the spec's on the chunks (gb.least).

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

def gfe.go(+k: Nat, +x: Nat, +seen: List<&2, Nat>, +n: Nat) -> {M.feed.of(M.shortest(x <> seen, k), k, x <> seen, n) == InferGuard.feed_spec.of(InferGuard.least(x <> seen, k, InferGuard.periods_spec(k)), k, x <> seen, n) : M.Next}:
  %LAGuard.gb.periods(k) : {M.feed.of(M.shortest(x <> seen, k), k, x <> seen, n) == InferGuard.feed_spec.of(InferGuard.least(x <> seen, k, _), k, x <> seen, n) : M.Next}
  %LAGuard.gb.least(x <> seen, k, If.periods(k)) : {M.feed.of(M.shortest(x <> seen, k), k, x <> seen, n) == InferGuard.feed_spec.of(_, k, x <> seen, n) : M.Next}
  %Equal.sym(Maybe<&2, Nat>, M.shortest(x <> seen, k), M.shortest.go(x <> seen, k, If.periods(k)), LAGuard.gb.cover(x, seen, k)) : {M.feed.of(_, k, x <> seen, n) == InferGuard.feed_spec.of(M.shortest.go(x <> seen, k, If.periods(k)), k, x <> seen, n) : M.Next}
  gfe.of(M.shortest.go(x <> seen, k, If.periods(k)), k, x <> seen, n)

def InferGuard.infer_guard_feed_exact(st, x):
  match st:
    case M.St{k, seen, n}:
      gfe.go(k, x, seen, n)
