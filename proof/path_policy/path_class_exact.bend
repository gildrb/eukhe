# eukhe: the proof of LAW path_class_exact
#
# PROOF: the model's class of a path is class_res of its real path; the
# real path is pp_real (path_real_exact), and on Res{at, l} class_res is the
# judgment's class (path_judge_class), which is pp_class
# (path_judge_class_exact).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./path_real_exact.bend as PPathRealExact
import ./path_judge_class_exact.bend as PPathJudgeClassExact

def pcl.res(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, r: Pp.Res) -> {Pp.class_res(Pp.Pol{ro, ru, se}, r) == PathPolicy.pp_class_res(ro, ru, se, r) : Pp.Cls}:
  match r:
    case Pp.Res{+at, +l}:
      PathPolicy.path_judge_class_exact(ro, ru, se, at, l)

def pcl.class(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>) -> {Pp.class(Pp.Pol{ro, ru, se}, ls, segs) == PathPolicy.pp_class_res(ro, ru, se, PathPolicy.pp_real(ls, segs)) : Pp.Cls}:
  %PathPolicy.path_real_exact(ls, segs) : {Pp.class(Pp.Pol{ro, ru, se}, ls, segs) == PathPolicy.pp_class_res(ro, ru, se, _) : Pp.Cls}
  pcl.res(ro, ru, se, Pp.real(ls, segs))

def PathPolicy.path_class_exact(ro, ru, se, ls, segs):
  pcl.class(ro, ru, se, ls, segs)
