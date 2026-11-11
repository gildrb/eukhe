# eukhe: the proof of LAW gateway_backoff_entry_capped
#
# PROOF: the entry answers the model's wait (gateway_backoff_entry_answers);
# for a double past 10 s big picks the code's cap, 10000.

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/gateway_backoff.bend as GatewayBackoff
import ./gateway_backoff_entry_answers.bend as PGatewayBackoffEntryAnswers

def GatewayBackoff.gateway_backoff_entry_capped(d, h, big):
  %big : {FGb.ffi(GatewayBackoff.gb_w_req(Some{d}, "")) == Wr.put_nat(Gb.next.cap(_, Nat.mul(2n, d)), "") : String}
  GatewayBackoff.gateway_backoff_entry_answers(Some{d}, h)
