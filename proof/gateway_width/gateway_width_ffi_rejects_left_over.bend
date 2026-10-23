# eukhe: the proof of LAW gateway_width_ffi_rejects_left_over

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_gateway_width.bend as FGw
import ../../LAWS.bend as Laws

def Laws.gateway_width_ffi_rejects_left_over(s, q, r, got, more):
  %Equal.sym(Wr.Dec<List<&2, List<&2, Nat>>>, FGw.get_req(s), Wr.Got{q, r}, got) : {Laws.wire_opens_err(FGw.answer(_)) == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(r), False{}, more) : {Laws.wire_opens_err(FGw.reply(_, q)) == True{} : Bool}
  {==}
