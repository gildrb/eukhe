# eukhe: the proof of LAW doc_plan_ffi_left_over_exact

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

# PROOF of LAW doc_plan_ffi_left_over_exact: the left-over error comes only from a question the decoder read with input after it; what it read is spelled and fits (dp.pr). A malformed request answers another text, and a whole question an answer, never an error form (dp.answer_not_err).

def dp.lo_end(-s: String, +q: FDp.Req, r: String, pr: {s == DocPlan.spell_req(q, r) : String} & {DocPlan.req_fits(q) == True{} : Bool}, e: {FDp.ffi.done(q, Wr.end(r)) == Wr.err("doc_plan: input left after the request") : String}) -> Sigma<&1, &1, DocPlan.LeftOver, w => {s == DocPlan.spell_left_over(w) : String} & {DocPlan.req_fits(DocPlan.left_req(w)) == True{} : Bool}>:
  match r:
    case SNil{}:
      LADocPlan.dp.absurd(Sigma<&1, &1, DocPlan.LeftOver, w => {s == DocPlan.spell_left_over(w) : String} & {DocPlan.req_fits(DocPlan.left_req(w)) == True{} : Bool}>, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FDp.ffi.done(q, True{})), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FDp.ffi.done(q, True{})), False{}, LADocPlan.dp.answer_not_err(q)), Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), FDp.ffi.done(q, True{}), Wr.err("doc_plan: input left after the request"), e)))
    case SCon{+h, +t}:
      (DocPlan.LeftOver{q, h, t}, pr)

def dp.lo(-s: String, d: Wr.Dec<FDp.Req>, pr: LADocPlan.dp.PR(s, d), e: {FDp.ffi.got(d) == Wr.err("doc_plan: input left after the request") : String}) -> Sigma<&1, &1, DocPlan.LeftOver, w => {s == DocPlan.spell_left_over(w) : String} & {DocPlan.req_fits(DocPlan.left_req(w)) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, +r}:
      dp.lo_end(s, q, r, pr, e)
    case Wr.Bad{}:
      LADocPlan.dp.absurd(Sigma<&1, &1, DocPlan.LeftOver, w => {s == DocPlan.spell_left_over(w) : String} & {DocPlan.req_fits(DocPlan.left_req(w)) == True{} : Bool}>, Equal.cong(String, Bool, z => LawsBase.text_same(z, Wr.err("doc_plan: input left after the request")), Wr.err("doc_plan: malformed request"), Wr.err("doc_plan: input left after the request"), e))

def DocPlan.doc_plan_ffi_left_over_exact(s, e):
  dp.lo(s, FDp.get_req(Wr.get_nat(s)), LADocPlan.dp.pr(s), e)
