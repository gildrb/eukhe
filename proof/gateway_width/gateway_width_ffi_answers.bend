# eukhe: the proof of LAW gateway_width_ffi_answers

import Base
import ../../bend/ffi_gateway_width.bend as FGw
import ../../bend/gateway_width.bend as Gw
import ../../bend/wire.bend as Wr
import ../../laws/gateway_width.bend as GatewayWidth
import ./gateway_width_ffi_request_round_trip.bend as PGatewayWidthFfiRequestRoundTrip

def GatewayWidth.gateway_width_ffi_answers(rows, h):
  %Equal.sym(Wr.Dec<List<&2, List<&2, Nat>>>, FGw.get_req(FGw.put_req(rows, "")), Wr.Got{rows, ""}, GatewayWidth.gateway_width_ffi_request_round_trip(rows, "", h)) : {FGw.answer(_) == FGw.put_lay(Gw.layout(FGw.table(rows)), "") : String}
  {==}
