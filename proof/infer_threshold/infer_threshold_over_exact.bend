# eukhe: the proof of LAW infer_threshold_over_exact
# The limit test is t + r > w and the background test t + r + c > w
# (LAThreshold.gt.above, gt.above_by: x - a <= t is x <= a + t).

import Base
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ./base.bend as LAThreshold

def gto.on(+v: Nat, +t: Nat, +r: M.Z, m: M.Z) -> {M.over.at(Nat.is_le(M.limit_at(1n+v, r), t), M.limit_at(1n+v, r), t, m) == InferThreshold.over_spec.on(InferThreshold.above(t, r, 1n+v), t, r, m, 1n+v) : M.Over}:
  %Equal.sym(Bool, Nat.is_le(M.limit_at(1n+v, r), t), InferThreshold.above(t, r, 1n+v), LAThreshold.gt.above(1n+v, r, t)) : {M.over.at(_, M.limit_at(1n+v, r), t, m) == InferThreshold.over_spec.on(InferThreshold.above(t, r, 1n+v), t, r, m, 1n+v) : M.Over}
  LAThreshold.gt.at(InferThreshold.above(t, r, 1n+v), 1n+v, r, m, t)

def InferThreshold.infer_threshold_over_exact(on, t, w, r, m):
  match on:
    case False{}:
      {==}
    case True{}:
      match w:
        case 0n:
          {==}
        case 1n+v:
          gto.on(v, t, r, m)
