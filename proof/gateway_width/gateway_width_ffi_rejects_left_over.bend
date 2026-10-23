# eukhe: the proof of LAW gateway_width_ffi_rejects_left_over

import Base
import ../../bend/ffi_gateway_width.bend as FGw
import ../../bend/wire.bend as Wr
import ../../laws/gateway_width.bend as GatewayWidth
import ../../laws/base.bend as LawsBase

def GatewayWidth.gateway_width_ffi_rejects_left_over(s, q, r, got, more):
  %Equal.sym(Wr.Dec<List<&2, List<&2, Nat>>>, FGw.get_req(s), Wr.Got{q, r}, got) : {LawsBase.wire_opens_err(FGw.answer(_)) == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(r), False{}, more) : {LawsBase.wire_opens_err(FGw.reply(_, q)) == True{} : Bool}
  {==}
