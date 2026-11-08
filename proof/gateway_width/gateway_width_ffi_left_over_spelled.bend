# eukhe: the proof of LAW gateway_width_ffi_left_over_spelled
#
# PROOF: the spec's spelling is the entry's put_req (gwa.req), which reads
# back with the rest untouched (gateway_width_ffi_request_round_trip); a
# rest that is not empty answers the left-over error.

import Base
import ../../bend/ffi_gateway_width.bend as FGw
import ../../bend/wire.bend as Wr
import ../../laws/gateway_width.bend as GatewayWidth
import ./gateway_width_ffi_request_round_trip.bend as PGatewayWidthFfiRequestRoundTrip
import ./gateway_width_ffi_answers_spelled.bend as PGatewayWidthFfiAnswersSpelled

def GatewayWidth.gateway_width_ffi_left_over_spelled(rows, fits, c, t):
  %PGatewayWidthFfiAnswersSpelled.gwa.req(rows, SCon{c, t}) : {FGw.ffi(_) == Wr.err("gateway_width: input left over") : String}
  %Equal.sym(Wr.Dec<List<&2, List<&2, Nat>>>, FGw.get_req(FGw.put_req(rows, SCon{c, t})), Wr.Got{rows, SCon{c, t}}, GatewayWidth.gateway_width_ffi_request_round_trip(rows, SCon{c, t}, PGatewayWidthFfiAnswersSpelled.gwa.fits(rows, fits))) : {FGw.answer(_) == Wr.err("gateway_width: input left over") : String}
  {==}
