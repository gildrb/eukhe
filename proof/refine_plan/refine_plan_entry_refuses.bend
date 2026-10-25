# eukhe: the proof of LAW refine_plan_entry_refuses
#
# PROOF: every answer opens with a count, a length, a tag or a Bool, never 'E' (rpe.reply_ok); so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/refine_plan.bend as Rp
import ../../bend/ffi_refine_plan.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/entry.bend as RefinePlanEntry
import ./base/enc.bend as LEnc
import ../base/staging.bend as LStg

def rpf.refuse(d: Wr.Dec<FRp.Req>, bad: {LawsBase.wire_opens_err(FRp.ffi.got(d)) == True{} : Bool}) -> {FRp.ffi.got(d) == Wr.err("refine_plan: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FRp.answer(q) == Wr.err("refine_plan: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FRp.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FRp.answer(q)), True{}, bad), LEnc.rpe.reply_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def RefinePlanEntry.refine_plan_entry_refuses(s, bad):
  rpf.refuse(FRp.get_req(s), bad)
