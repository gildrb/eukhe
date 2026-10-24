# eukhe: the proof of LAW infer_threshold_early_steps
# Induction on the run, generalized over the index of its first request:
# with a positive margin a request is over some threshold exactly when it
# reaches the background one (LAThreshold.gt.over: over the limit, it is
# over the lower background threshold too), the test first_at makes.

import Base
import ../../bend/infer.bend as If
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ./base.bend as LAThreshold

def gte.at(h: Bool, -i: Nat, -x: Nat, -rest: List<&2, Nat>, -w: Nat, -r: M.Z, -m: M.Z, -T: Nat,
  ih: {InferThreshold.first_over(rest, 1n+i, w, r, m, InferThreshold.head.over(rest, w, r, m)) == If.first_at.go(rest, T, 1n+i, If.reach.at(rest, T)) : Maybe<&2, Nat>})
  -> {InferThreshold.first_over(x <> rest, i, w, r, m, h) == If.first_at.go(x <> rest, T, i, h) : Maybe<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      ih

def gte.go(xs: List<&2, Nat>, +i: Nat, +v: Nat, +r: M.Z, +b: Nat) -> {InferThreshold.first_over(xs, i, 1n+v, r, M.Up{1n+b}, InferThreshold.head.over(xs, 1n+v, r, M.Up{1n+b})) == If.first_at.go(xs, Nat.sub(InferThreshold.lim_spec(1n+v, r), 1n+b), i, If.reach.at(xs, Nat.sub(InferThreshold.lim_spec(1n+v, r), 1n+b))) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, InferThreshold.is_over(M.over.at(Nat.is_le(M.limit_at(1n+v, r), x), M.limit_at(1n+v, r), x, M.Up{1n+b})), Nat.is_le(Nat.sub(InferThreshold.lim_spec(1n+v, r), 1n+b), x), LAThreshold.gt.over(1n+v, r, b, x)) : {InferThreshold.first_over(x <> rest, i, 1n+v, r, M.Up{1n+b}, _) == If.first_at.go(x <> rest, Nat.sub(InferThreshold.lim_spec(1n+v, r), 1n+b), i, Nat.is_le(Nat.sub(InferThreshold.lim_spec(1n+v, r), 1n+b), x)) : Maybe<&2, Nat>}
      gte.at(Nat.is_le(Nat.sub(InferThreshold.lim_spec(1n+v, r), 1n+b), x), i, x, rest, 1n+v, r, M.Up{1n+b}, Nat.sub(InferThreshold.lim_spec(1n+v, r), 1n+b), gte.go(rest, 1n+i, v, r, b))

def InferThreshold.infer_threshold_early_steps(xs, v, r, b):
  gte.go(xs, 0n, v, r, b)
