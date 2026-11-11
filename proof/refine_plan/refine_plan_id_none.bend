# eukhe: the proof of LAW refine_plan_id_none
#
# PROOF: no id and no create: no computed id, whatever the other facts.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan

def RefinePlan.refine_plan_id_none(c, t, content, p, a, ex, df, hd):
  {==}
