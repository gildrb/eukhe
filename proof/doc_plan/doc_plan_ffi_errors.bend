# eukhe: the proof of LAW doc_plan_ffi_errors

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

# PROOF of LAW doc_plan_ffi_errors: the entry answers the malformed error form, the left-over error form, or an answer, which never opens with 'E' (dp.answer_not_err).

def dp.errs_end(r: String, +q: FDp.Req, e: {LawsBase.wire_opens_err(FDp.ffi.done(q, Wr.end(r))) == True{} : Bool}) -> {Bool.or(LawsBase.text_same(FDp.ffi.done(q, Wr.end(r)), Wr.err("doc_plan: malformed request")), LawsBase.text_same(FDp.ffi.done(q, Wr.end(r)), Wr.err("doc_plan: input left after the request"))) == True{} : Bool}:
  match r:
    case SNil{}:
      LADocPlan.dp.absurd({Bool.or(LawsBase.text_same(FDp.ffi.done(q, True{}), Wr.err("doc_plan: malformed request")), LawsBase.text_same(FDp.ffi.done(q, True{}), Wr.err("doc_plan: input left after the request"))) == True{} : Bool}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FDp.ffi.done(q, True{})), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FDp.ffi.done(q, True{})), False{}, LADocPlan.dp.answer_not_err(q)), e))
    case SCon{h, t}:
      match q:
        case FDp.QContent{st, v, o}:
          {==}
        case FDp.QPublishes{re, c, w}:
          {==}

def dp.errs(d: Wr.Dec<FDp.Req>, e: {LawsBase.wire_opens_err(FDp.ffi.got(d)) == True{} : Bool}) -> {Bool.or(LawsBase.text_same(FDp.ffi.got(d), Wr.err("doc_plan: malformed request")), LawsBase.text_same(FDp.ffi.got(d), Wr.err("doc_plan: input left after the request"))) == True{} : Bool}:
  match d:
    case Wr.Got{+q, +r}:
      dp.errs_end(r, q, e)
    case Wr.Bad{}:
      {==}

def DocPlan.doc_plan_ffi_errors(s, e):
  dp.errs(FDp.get_req(Wr.get_nat(s)), e)
