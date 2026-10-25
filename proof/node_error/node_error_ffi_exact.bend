# eukhe: the proof of LAW node_error_ffi_exact

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

# PROOF of LAW node_error_ffi_exact: what the decoder reads is spelled, fits, and so is the input after it (ne.pr); a reply that is no error form has nothing after the request.

def ne.ex_end(-s: String, r: String, +q: FNe.Req, pr: {s == NodeError.spell_req(q, r) : String} & {NodeError.req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FNe.ffi.done(q, Wr.end(r))) == False{} : Bool}) -> Sigma<&1, &1, FNe.Req, q => {s == NodeError.spell_req(q, "") : String} & {NodeError.req_fits(q) == True{} : Bool}>:
  match r:
    case SNil{}:
      (q, pr)
    case SCon{h, t}:
      match q:
        case FNe.Req{c, f}:
          LANodeError.ne.absurd_t(Sigma<&1, &1, FNe.Req, q => {s == NodeError.spell_req(q, "") : String} & {NodeError.req_fits(q) == True{} : Bool}>, ok)

def ne.ex(-s: String, d: Wr.Dec<FNe.Req>, pr: LANodeError.ne.PR(s, d), ok: {LawsBase.wire_opens_err(FNe.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FNe.Req, q => {s == NodeError.spell_req(q, "") : String} & {NodeError.req_fits(q) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, +r}:
      ne.ex_end(s, r, q, pr, ok)
    case Wr.Bad{}:
      LANodeError.ne.absurd_t(Sigma<&1, &1, FNe.Req, q => {s == NodeError.spell_req(q, "") : String} & {NodeError.req_fits(q) == True{} : Bool}>, ok)

def NodeError.node_error_ffi_exact(s, ok):
  ne.ex(s, FNe.get_req(FNe.get_code(Wr.get_nat(s))), LANodeError.ne.pr(s), ok)
