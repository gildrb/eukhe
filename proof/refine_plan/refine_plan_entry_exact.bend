# eukhe: the proof of LAW refine_plan_entry_exact
#
# PROOF: each decoder stage's answer is the spelling of what it read (rpx.*, from the wire exactness laws); an answer that is no error read a whole request with nothing left (rpx.top).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../bend/ffi_refine_plan.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/entry.bend as RefinePlanEntry
import ./base/x2.bend as LX
import ../base/wire_dec.bend as LD

def RefinePlanEntry.refine_plan_entry_exact(s, ok):
  LX.rpx.top(s, FRp.get_req(s), LX.rpx.req.at(s, Wr.get_nat(s), LD.dcw.nat(s)), ok)
