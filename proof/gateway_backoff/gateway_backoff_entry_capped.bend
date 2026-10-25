# eukhe: the proof of LAW gateway_backoff_entry_capped
#
# PROOF: the entry answers the spec's wait (gateway_backoff_entry_answers);
# the spec's wait for a double past 10 s is 10000 (big picks the cap).

import Base
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/gateway_backoff.bend as GatewayBackoff

def GatewayBackoff.gateway_backoff_entry_capped(d, h, big):
  %big : {FGb.ffi(GatewayBackoff.gb_w_req(Some{d}, "")) == Wr.put_nat(GatewayBackoff.gb_cap(_, Nat.mul(2n, d)), "") : String}
  GatewayBackoff.gateway_backoff_entry_answers(Some{d}, h)
