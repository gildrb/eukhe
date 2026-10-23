# eukhe: the proof of LAW gateway_width_ffi_request_round_trip

import Base
import ../../bend/ffi_gateway_width.bend as FGw
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/gateway_width.bend as GatewayWidth
import ../../laws/wire.bend as Wire
import ../base.bend as L

# gateway_width
# -------------

def GatewayWidth.gateway_width_ffi_request_round_trip(rows, rest, h):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, Fl.flat(rows), rest)), Wr.Got{Fl.flat(rows), rest}, Wire.wire_list_round_trip(Fl.flat(rows), rest, h)) : {FGw.get_req.ns(_) == Wr.Got{rows, rest} : Wr.Dec<List<&2, List<&2, Nat>>>}
  %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, Fl.unflat(Fl.flat(rows)), Some{rows}, L.fe.unflat_flat(rows)) : {FGw.get_req.of(_, rest) == Wr.Got{rows, rest} : Wr.Dec<List<&2, List<&2, Nat>>>}
  {==}
