# eukhe: the proof of LAW refine_plan_plan_lines
#
# PROOF: the code's fold of change lines is the lines of the filtered
# applied rows (LPlan.rpp.lines).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/plan.bend as RefinePlanPlan
import ./base/plan.bend as LPlan

def RefinePlanPlan.refine_plan_plan_lines(o, eds):
  LPlan.rpp.changes(o, eds)
