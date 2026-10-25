# eukhe: the proof of LAW refine_plan_entry_left_over
#
# PROOF: the spelled request reads back with the extra input left (rpe.req_rt), which the entry refuses.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../bend/ffi_refine_plan.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/entry.bend as RefinePlanEntry
import ./base/rt.bend as LRt

def RefinePlanEntry.refine_plan_entry_left_over(q, c, t, fit):
  %Equal.sym(Wr.Dec<FRp.Req>, FRp.get_req(RefinePlanEntry.rp_w_req(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, LRt.rpe.req_rt(q, SCon{c, t}, fit)) : {FRp.ffi.got(_) == Wr.err("refine_plan: malformed request") : String}
  {==}
