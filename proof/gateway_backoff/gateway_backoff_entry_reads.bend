# eukhe: the proof of LAW gateway_backoff_entry_reads
#
# PROOF: the tag computes; the last wait reads back by
# wire_nat_round_trip (it fits by the premise).

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_backoff.bend as GatewayBackoff
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def GatewayBackoff.gateway_backoff_entry_reads(m, rest, h):
  match m:
    case None{}:
      {==}
    case Some{+d}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(d, rest)), Wr.Got{d, rest}, Wire.wire_nat_round_trip(d, rest, h)) : {FGb.get_req.some(_) == Wr.Got{Some{d}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}
