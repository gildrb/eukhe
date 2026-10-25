# eukhe: the proof of LAW refine_plan_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (rpe.req_rt), so the entry answers the model's answer, the spec's (the model laws), spelled by encoders that are the spec spellers (rpe.*).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../bend/ffi_refine_plan.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/refine_plan/model.bend as RefinePlan
import ../../laws/refine_plan/entry.bend as RefinePlanEntry
import ./base/enc.bend as LEnc
import ./base/rt.bend as LRt
import ./refine_plan_ids_spec.bend as PRefinePlanIdsSpec
import ./refine_plan_plan_spec.bend as PRefinePlanPlanSpec
import ./refine_plan_back_spec.bend as PRefinePlanBackSpec
import ./refine_plan_norm_spec.bend as PRefinePlanNormSpec
import ./refine_plan_incomplete_spec.bend as PRefinePlanIncompleteSpec
import ./refine_plan_fit_spec.bend as PRefinePlanFitSpec

def rpa.reply(q: FRp.Req) -> {FRp.answer(q) == RefinePlanEntry.rp_w_reply(q) : String}:
  match q:
    case FRp.QIds{+eds}:
      %RefinePlan.refine_plan_ids_spec(eds) : {FRp.put_mss(Rp.ids(eds), "") == RefinePlanEntry.rp_w_mss(_, "") : String}
      LEnc.rpe.mss(Rp.ids(eds), "")
    case FRp.QPlan{+o, +eds}:
      %RefinePlan.refine_plan_plan_spec(o, eds) : {FRp.put_plan(Rp.plan(o, eds), "") == RefinePlanEntry.rp_w_plan(_, "") : String}
      LEnc.rpe.plan(Rp.plan(o, eds), "")
    case FRp.QBack{+id, +was}:
      %RefinePlan.refine_plan_back_spec(id, was) : {FRp.put_back(Rp.back(id, was), "") == RefinePlanEntry.rp_w_back(_, "") : String}
      LEnc.rpe.back(Rp.back(id, was), "")
    case FRp.QNorm{+s, +r, +o}:
      %RefinePlan.refine_plan_norm_spec(s, r, o) : {FRp.put_texts(Rp.norm(s, r, o), "") == RefinePlanEntry.rp_w_texts(_, "") : String}
      LEnc.rpe.texts(Rp.norm(s, r, o), "")
    case FRp.QScan{+t}:
      %RefinePlan.refine_plan_incomplete_spec(t) : {Wr.put_bool(Rp.incomplete(t), "") == Wr.put_bool(_, "") : String}
      {==}
    case FRp.QFit{+w, +c, +st, +p}:
      %RefinePlan.refine_plan_fit_spec(w, c, st, p) : {FRp.put_step(Rp.fit(w, c, st, p), "") == RefinePlanEntry.rp_w_step(_, "") : String}
      LEnc.rpe.step(Rp.fit(w, c, st, p), "")

def RefinePlanEntry.refine_plan_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FRp.Req>, FRp.get_req(RefinePlanEntry.rp_w_req(q, "")), Wr.Got{q, ""}, LRt.rpe.req_rt(q, "", fit)) : {FRp.ffi.got(_) == RefinePlanEntry.rp_w_reply(q) : String}
  rpa.reply(q)
