# eukhe: the proof of LAW gateway_width_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled tables that fit, the rest after
# them untouched (gro.req of gateway_width_ffi_reads_only_requests); when
# it reads none the entry answers the malformed error, which the premise
# excludes.

import Base
import ../../bend/ffi_gateway_width.bend as FGw
import ../../bend/wire.bend as Wr
import ../../laws/gateway_width.bend as GatewayWidth
import ../wire/base/spell.bend as LAWireSpell
import ./gateway_width_ffi_reads_only_requests.bend as PGatewayWidthFfiReadsOnlyRequests

def gmu.goal(+s: String) -> Type:
  &rows: List<&2, List<&2, Nat>> -> &rest: String -> {(s, GatewayWidth.gw_req_fits(rows)) == (GatewayWidth.gw_spell_req(rows, rest), True{}) : String & Bool}

def gmu.eq(+s: String, +rows: List<&2, List<&2, Nat>>, +rest: String, e1: {s == GatewayWidth.gw_spell_req(rows, rest) : String}, e2: {GatewayWidth.gw_req_fits(rows) == True{} : Bool}) -> {(s, GatewayWidth.gw_req_fits(rows)) == (GatewayWidth.gw_spell_req(rows, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, GatewayWidth.gw_spell_req(rows, rest), e1) : {(_, GatewayWidth.gw_req_fits(rows)) == (GatewayWidth.gw_spell_req(rows, rest), True{}) : String & Bool}
  %Equal.sym(Bool, GatewayWidth.gw_req_fits(rows), True{}, e2) : {(GatewayWidth.gw_spell_req(rows, rest), _) == (GatewayWidth.gw_spell_req(rows, rest), True{}) : String & Bool}
  {==}

def gmu.main(+s: String, d: Wr.Dec<List<&2, List<&2, Nat>>>, inv: PGatewayWidthFfiReadsOnlyRequests.gro.Req(s, d), other: {String.eq(FGw.answer(d), Wr.err("gateway_width: malformed request")) == False{} : Bool}) -> gmu.goal(s):
  match d:
    case Wr.Got{+rows, +rest}:
      (e1, e2) = inv
      (rows, (rest, gmu.eq(s, rows, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(gmu.goal(s), other)

def GatewayWidth.gateway_width_ffi_malformed_unless_request(s, other):
  gmu.main(s, FGw.get_req(s), PGatewayWidthFfiReadsOnlyRequests.gro.req(s), other)
