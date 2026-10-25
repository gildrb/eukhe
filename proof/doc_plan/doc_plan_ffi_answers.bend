# eukhe: the proof of LAW doc_plan_ffi_answers

import Base
import ../../bend/doc_plan.bend as Dp
import ../../bend/ffi_doc_plan.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../base/wire.bend as LWire
import ../../laws/doc_plan.bend as DocPlan
import ./base.bend as LADocPlan
import ./doc_plan_content_exact.bend as PDocPlanContentExact
import ./doc_plan_publishes_exact.bend as PDocPlanPublishesExact

# PROOF of LAW doc_plan_ffi_answers: the question reads back with nothing left (dp.reads), the model's answer is the spec's (doc_plan_content_exact, doc_plan_publishes_exact) and the reply writer is the spec's speller (dp.put_content).

def DocPlan.doc_plan_ffi_answers(q, fit):
  match q:
    case FDp.QContent{+s, +v, +o}:
      %Equal.sym(String, FDp.ffi(DocPlan.spell_req(FDp.QContent{s, v, o}, "")), FDp.ffi.done(FDp.QContent{s, v, o}, Wr.end("")), LADocPlan.dp.reads(FDp.QContent{s, v, o}, "", fit)) : {_ == DocPlan.spell_content(DocPlan.content_spec(s, v, o)) : String}
      %DocPlan.doc_plan_content_exact(s, v, o) : {FDp.put_content(Dp.content(s, v, o)) == DocPlan.spell_content(_) : String}
      LADocPlan.dp.put_content(Dp.content(s, v, o))
    case FDp.QPublishes{+re, +c, +w}:
      %Equal.sym(String, FDp.ffi(DocPlan.spell_req(FDp.QPublishes{re, c, w}, "")), FDp.ffi.done(FDp.QPublishes{re, c, w}, Wr.end("")), LADocPlan.dp.reads(FDp.QPublishes{re, c, w}, "", fit)) : {_ == Wr.put_bool(DocPlan.publishes_spec(re, c, w), "") : String}
      %DocPlan.doc_plan_publishes_exact(re, c, w) : {Wr.put_bool(Dp.publishes(re, c, w), "") == Wr.put_bool(_, "") : String}
      {==}
