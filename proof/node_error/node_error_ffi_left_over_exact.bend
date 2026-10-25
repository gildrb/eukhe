# eukhe: the proof of LAW node_error_ffi_left_over_exact

import Base
import ../../bend/node_error.bend as Ne
import ../../bend/ffi_node_error.bend as FNe
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/node_error.bend as NodeError
import ./base.bend as LANodeError

# PROOF of LAW node_error_ffi_left_over_exact: the left-over error comes only from a request the decoder read with input after it; what it read is spelled and fits (ne.pr). A malformed request answers another text, and a whole request an answer, never an error form (ne.answer_not_err).

def ne.lo_end(-s: String, +q: FNe.Req, r: String, pr: {s == NodeError.spell_req(q, r) : String} & {NodeError.req_fits(q) == True{} : Bool}, e: {FNe.ffi.done(q, Wr.end(r)) == Wr.err("node_error: input left after the request") : String}) -> Sigma<&1, &1, NodeError.LeftOver, w => {s == NodeError.spell_left_over(w) : String} & {NodeError.req_fits(NodeError.left_req(w)) == True{} : Bool}>:
  match r:
    case SNil{}:
      LANodeError.ne.absurd(Sigma<&1, &1, NodeError.LeftOver, w => {s == NodeError.spell_left_over(w) : String} & {NodeError.req_fits(NodeError.left_req(w)) == True{} : Bool}>, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FNe.ffi.done(q, True{})), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FNe.ffi.done(q, True{})), False{}, LANodeError.ne.answer_not_err(q)), Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), FNe.ffi.done(q, True{}), Wr.err("node_error: input left after the request"), e)))
    case SCon{+h, +t}:
      (NodeError.LeftOver{q, h, t}, pr)

def ne.lo(-s: String, d: Wr.Dec<FNe.Req>, pr: LANodeError.ne.PR(s, d), e: {FNe.ffi.got(d) == Wr.err("node_error: input left after the request") : String}) -> Sigma<&1, &1, NodeError.LeftOver, w => {s == NodeError.spell_left_over(w) : String} & {NodeError.req_fits(NodeError.left_req(w)) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, +r}:
      ne.lo_end(s, q, r, pr, e)
    case Wr.Bad{}:
      LANodeError.ne.absurd(Sigma<&1, &1, NodeError.LeftOver, w => {s == NodeError.spell_left_over(w) : String} & {NodeError.req_fits(NodeError.left_req(w)) == True{} : Bool}>, Equal.cong(String, Bool, z => LawsBase.text_same(z, Wr.err("node_error: input left after the request")), Wr.err("node_error: malformed request"), Wr.err("node_error: input left after the request"), e))

def NodeError.node_error_ffi_left_over_exact(s, e):
  ne.lo(s, FNe.get_req(FNe.get_code(Wr.get_nat(s))), LANodeError.ne.pr(s), e)
