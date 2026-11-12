# eukhe: the proof of LAW refine_plan_ids_split
#
# PROOF: induction on xs.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan

def rpd.split(xs: List<&2, Rp.Ed>, +ys: List<&2, Rp.Ed>) -> {Rp.ids(List.append(&2, Rp.Ed, xs, ys)) == List.append(&2, Maybe<&2, String>, Rp.ids(xs), Rp.ids(ys)) : List<&2, Maybe<&2, String>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      Equal.cong(List<&2, Maybe<&2, String>>, List<&2, Maybe<&2, String>>, l => Rp.computed(x) <> l, Rp.ids(List.append(&2, Rp.Ed, t, ys)), List.append(&2, Maybe<&2, String>, Rp.ids(t), Rp.ids(ys)), rpd.split(t, ys))

def RefinePlan.refine_plan_ids_split(xs, ys):
  rpd.split(xs, ys)
