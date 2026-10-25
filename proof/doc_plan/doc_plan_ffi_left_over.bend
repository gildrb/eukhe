# eukhe: the proof of LAW doc_plan_ffi_left_over

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

# PROOF of LAW doc_plan_ffi_left_over: the question reads back with the rest untouched (dp.reads); the rest is not empty, so the entry answers the left-over error form.

def DocPlan.doc_plan_ffi_left_over(q, h, t, fit):
  match q:
    case FDp.QContent{+s, +v, +o}:
      %Equal.sym(String, FDp.ffi(DocPlan.spell_req(FDp.QContent{s, v, o}, SCon{h, t})), FDp.ffi.done(FDp.QContent{s, v, o}, Wr.end(SCon{h, t})), LADocPlan.dp.reads(FDp.QContent{s, v, o}, SCon{h, t}, fit)) : {_ == Wr.err("doc_plan: input left after the request") : String}
      {==}
    case FDp.QPublishes{+re, +c, +w}:
      %Equal.sym(String, FDp.ffi(DocPlan.spell_req(FDp.QPublishes{re, c, w}, SCon{h, t})), FDp.ffi.done(FDp.QPublishes{re, c, w}, Wr.end(SCon{h, t})), LADocPlan.dp.reads(FDp.QPublishes{re, c, w}, SCon{h, t}, fit)) : {_ == Wr.err("doc_plan: input left after the request") : String}
      {==}
