# eukhe: the proof of LAW doc_plan_ffi_exact

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

# PROOF of LAW doc_plan_ffi_exact: what the decoder reads is spelled, fits, and so is the input after it (dp.pr); a reply that is no error form has nothing after the question.

def dp.ex_end(-s: String, r: String, +q: FDp.Req, pr: {s == DocPlan.spell_req(q, r) : String} & {DocPlan.req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FDp.ffi.done(q, Wr.end(r))) == False{} : Bool}) -> Sigma<&1, &1, FDp.Req, q => {s == DocPlan.spell_req(q, "") : String} & {DocPlan.req_fits(q) == True{} : Bool}>:
  match r:
    case SNil{}:
      (q, pr)
    case SCon{h, t}:
      match q:
        case FDp.QContent{st, v, o}:
          LADocPlan.dp.absurd_t(Sigma<&1, &1, FDp.Req, q => {s == DocPlan.spell_req(q, "") : String} & {DocPlan.req_fits(q) == True{} : Bool}>, ok)
        case FDp.QPublishes{re, c, w}:
          LADocPlan.dp.absurd_t(Sigma<&1, &1, FDp.Req, q => {s == DocPlan.spell_req(q, "") : String} & {DocPlan.req_fits(q) == True{} : Bool}>, ok)

def dp.ex(-s: String, d: Wr.Dec<FDp.Req>, pr: LADocPlan.dp.PR(s, d), ok: {LawsBase.wire_opens_err(FDp.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FDp.Req, q => {s == DocPlan.spell_req(q, "") : String} & {DocPlan.req_fits(q) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, +r}:
      dp.ex_end(s, r, q, pr, ok)
    case Wr.Bad{}:
      LADocPlan.dp.absurd_t(Sigma<&1, &1, FDp.Req, q => {s == DocPlan.spell_req(q, "") : String} & {DocPlan.req_fits(q) == True{} : Bool}>, ok)

def DocPlan.doc_plan_ffi_exact(s, ok):
  dp.ex(s, FDp.get_req(Wr.get_nat(s)), LADocPlan.dp.pr(s), ok)
