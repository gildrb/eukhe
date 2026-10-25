# eukhe: the proof of LAW refine_plan_incomplete_spec
#
# PROOF: the model's functions are the spec helpers, function by function (rpb.incomplete).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../bend/ffi_refine_plan.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/entry.bend as RefinePlanEntry
import ./base.bend as LA

def RefinePlan.refine_plan_incomplete_spec(text):
  LA.rpb.incomplete(text)
