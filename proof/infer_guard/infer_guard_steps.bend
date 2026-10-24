# eukhe: the proof of LAW infer_guard_steps
# Induction on the stream, generalized over the chunks read: a chunk cuts
# exactly when the counters fire (LAGuard.gb.fires), at the same count;
# else both go on with it newest first.

import Base
import ../../bend/infer.bend as If
import ../../bend/infer_guard.bend as M
import ../../laws/infer_guard.bend as InferGuard
import ./base.bend as LAGuard

# a cut ends the drive, whatever chunks are left
def gst.cut(rest: List<&2, Nat>, -at: Nat, -p: Nat) -> {InferGuard.drive(rest, M.Cuts{at, p}) == If.CutAt{at} : If.Cut}:
  match rest:
    case Nil{}:
      {==}
    case y <> r:
      {==}

def gst.chunk(m: Maybe<&2, Nat>, -hit: Bool, rest: List<&2, Nat>, -k: Nat, -x: Nat, -seen: List<&2, Nat>, -n: Nat,
  e: {LAGuard.gb.some(m) == hit : Bool},
  ih: {InferGuard.drive(rest, M.Goes{M.St{k, x <> seen, 1n+n}}) == If.guard.go(rest, k, x <> seen, 1n+n, If.fire.at(rest, k, x <> seen)) : If.Cut})
  -> {InferGuard.drive(rest, M.feed.of(m, k, x <> seen, n)) == If.guard.go(x <> rest, k, seen, n, hit) : If.Cut}:
  match m:
    case None{}:
      %e : {InferGuard.drive(rest, M.Goes{M.St{k, x <> seen, 1n+n}}) == If.guard.go(x <> rest, k, seen, n, _) : If.Cut}
      ih
    case Some{p}:
      %e : {InferGuard.drive(rest, M.Cuts{1n+n, p}) == If.guard.go(x <> rest, k, seen, n, _) : If.Cut}
      gst.cut(rest, 1n+n, p)

def gst.go(xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>, +n: Nat) -> {InferGuard.drive(xs, M.Goes{M.St{k, seen, n}}) == If.guard.go(xs, k, seen, n, If.fire.at(xs, k, seen)) : If.Cut}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      gst.chunk(M.shortest(x <> seen, k), If.fires(x <> seen, k), rest, k, x, seen, n,
        LAGuard.gb.fires(x <> seen, k, If.periods(k)), gst.go(rest, k, x <> seen, 1n+n))

def InferGuard.infer_guard_steps(xs, k):
  gst.go(xs, k, Nil{}, 0n)
