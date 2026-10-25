# eukhe: the proof of LAW gateway_backoff_example
#
# PROOF: closed: both sides compute.

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_backoff.bend as GatewayBackoff

def GatewayBackoff.gateway_backoff_example():
  {==}
