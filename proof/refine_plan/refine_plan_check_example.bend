# eukhe: the proof of LAW refine_plan_check_example
#
# PROOF: closed: both sides compute.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../bend/ffi_refine_plan.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/entry.bend as RefinePlanEntry

def RefinePlan.refine_plan_check_example():
  {==}
