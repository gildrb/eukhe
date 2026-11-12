# eukhe: the proof of LAW refine_plan_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (rpe.req_rt), so the entry answers the model's answer, spelled by encoders that are the reply spellers (rpe.*).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../bend/ffi_refine_plan.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/refine_plan/entry.bend as RefinePlanEntry
import ./base/enc.bend as LEnc
import ./base/rt.bend as LRt

def rpa.reply(q: FRp.Req) -> {FRp.answer(q) == RefinePlanEntry.rp_w_reply(q) : String}:
  match q:
    case FRp.QIds{+eds}:
      LEnc.rpe.mss(Rp.ids(eds), "")
    case FRp.QPlan{+o, +eds}:
      LEnc.rpe.plan(Rp.plan(o, eds), "")
    case FRp.QBack{+id, +was}:
      LEnc.rpe.back(Rp.back(id, was), "")
    case FRp.QNorm{+s, +r, +o}:
      LEnc.rpe.texts(Rp.norm(s, r, o), "")
    case FRp.QScan{+t}:
      {==}
    case FRp.QFit{+w, +c, +st, +p}:
      LEnc.rpe.step(Rp.fit(w, c, st, p), "")

def RefinePlanEntry.refine_plan_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FRp.Req>, FRp.get_req(RefinePlanEntry.rp_w_req(q, "")), Wr.Got{q, ""}, LRt.rpe.req_rt(q, "", fit)) : {FRp.ffi.got(_) == RefinePlanEntry.rp_w_reply(q) : String}
  rpa.reply(q)
