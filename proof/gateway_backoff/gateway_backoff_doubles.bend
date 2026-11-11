# eukhe: the proof of LAW gateway_backoff_doubles
#
# PROOF: small picks the doubled wait of the code's cap.

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../laws/gateway_backoff.bend as GatewayBackoff

def GatewayBackoff.gateway_backoff_doubles(d, small):
  %small : {Gb.next(Some{d}) == Gb.next.cap(_, Nat.mul(2n, d)) : Nat}
  {==}
