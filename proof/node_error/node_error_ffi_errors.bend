# eukhe: the proof of LAW node_error_ffi_errors

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

# PROOF of LAW node_error_ffi_errors: the entry answers the malformed error form, the left-over error form, or an answer, which never opens with 'E' (ne.answer_not_err).

def ne.errs_end(r: String, +q: FNe.Req, e: {LawsBase.wire_opens_err(FNe.ffi.done(q, Wr.end(r))) == True{} : Bool}) -> {Bool.or(LawsBase.text_same(FNe.ffi.done(q, Wr.end(r)), Wr.err("node_error: malformed request")), LawsBase.text_same(FNe.ffi.done(q, Wr.end(r)), Wr.err("node_error: input left after the request"))) == True{} : Bool}:
  match r:
    case SNil{}:
      LANodeError.ne.absurd({Bool.or(LawsBase.text_same(FNe.ffi.done(q, True{}), Wr.err("node_error: malformed request")), LawsBase.text_same(FNe.ffi.done(q, True{}), Wr.err("node_error: input left after the request"))) == True{} : Bool}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FNe.ffi.done(q, True{})), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FNe.ffi.done(q, True{})), False{}, LANodeError.ne.answer_not_err(q)), e))
    case SCon{h, t}:
      match q:
        case FNe.Req{c, f}:
          {==}

def ne.errs(d: Wr.Dec<FNe.Req>, e: {LawsBase.wire_opens_err(FNe.ffi.got(d)) == True{} : Bool}) -> {Bool.or(LawsBase.text_same(FNe.ffi.got(d), Wr.err("node_error: malformed request")), LawsBase.text_same(FNe.ffi.got(d), Wr.err("node_error: input left after the request"))) == True{} : Bool}:
  match d:
    case Wr.Got{+q, +r}:
      ne.errs_end(r, q, e)
    case Wr.Bad{}:
      {==}

def NodeError.node_error_ffi_errors(s, e):
  ne.errs(FNe.get_req(FNe.get_code(Wr.get_nat(s))), e)
