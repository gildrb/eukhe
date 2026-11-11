# eukhe: the proof of LAW infer_threshold_blocks_steps
# Induction on the run, generalized over the index of its first request:
# a request is over the blocking threshold exactly when it reaches the
# limit (LAThreshold.gt.blocks), the test first_at makes.

import Base
import ../../bend/infer.bend as If
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ./base.bend as LAThreshold

def gtb.at(h: Bool, -i: Nat, -x: Nat, -rest: List<&2, Nat>, -w: Nat, -r: M.Z, -m: M.Z, -T: Nat,
  ih: {InferThreshold.first_blocks(rest, 1n+i, w, r, m, InferThreshold.head.blocks(rest, w, r, m)) == If.first_at.go(rest, T, 1n+i, If.reach.at(rest, T)) : Maybe<&2, Nat>})
  -> {InferThreshold.first_blocks(x <> rest, i, w, r, m, h) == If.first_at.go(x <> rest, T, i, h) : Maybe<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      ih

def gtb.go(xs: List<&2, Nat>, +i: Nat, +v: Nat, +r: M.Z, +m: M.Z) -> {InferThreshold.first_blocks(xs, i, 1n+v, r, m, InferThreshold.head.blocks(xs, 1n+v, r, m)) == If.first_at.go(xs, InferThreshold.lim_spec(1n+v, r), i, If.reach.at(xs, InferThreshold.lim_spec(1n+v, r))) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, InferThreshold.is_blocks(M.over.at(Nat.is_le(M.limit_at(1n+v, r), x), M.limit_at(1n+v, r), x, m)), Nat.is_le(InferThreshold.lim_spec(1n+v, r), x), LAThreshold.gt.blocks(1n+v, r, m, x)) : {InferThreshold.first_blocks(x <> rest, i, 1n+v, r, m, _) == If.first_at.go(x <> rest, InferThreshold.lim_spec(1n+v, r), i, Nat.is_le(InferThreshold.lim_spec(1n+v, r), x)) : Maybe<&2, Nat>}
      gtb.at(Nat.is_le(InferThreshold.lim_spec(1n+v, r), x), i, x, rest, 1n+v, r, m, InferThreshold.lim_spec(1n+v, r), gtb.go(rest, 1n+i, v, r, m))

def InferThreshold.infer_threshold_blocks_steps(xs, v, r, m):
  gtb.go(xs, 0n, v, r, m)
