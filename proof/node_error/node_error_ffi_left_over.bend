# eukhe: the proof of LAW node_error_ffi_left_over

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

# PROOF of LAW node_error_ffi_left_over: the request reads back with the rest untouched (ne.reads); the rest is not empty, so the entry answers the left-over error form.

def NodeError.node_error_ffi_left_over(q, h, t, fit):
  match q:
    case FNe.Req{+c, +f}:
      %Equal.sym(String, FNe.ffi(NodeError.spell_req(FNe.Req{c, f}, SCon{h, t})), FNe.ffi.done(FNe.Req{c, f}, Wr.end(SCon{h, t})), LANodeError.ne.reads(FNe.Req{c, f}, SCon{h, t}, fit)) : {_ == Wr.err("node_error: input left after the request") : String}
      {==}
