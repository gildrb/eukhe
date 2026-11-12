# eukhe: the proof of LAW refine_plan_plan_rows
#
# PROOF: the rows after the edits before t, then t, are the spec's rows of
# t from those (LPlan.rpp.fold, by one-more-edit LPlan.rpp.rows), from no
# edits.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/plan.bend as RefinePlanPlan
import ./base/plan.bend as LPlan

def RefinePlanPlan.refine_plan_plan_rows(o, eds):
  LPlan.rpp.fold(eds, o, [])
