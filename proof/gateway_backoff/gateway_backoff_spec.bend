# eukhe: the proof of LAW gateway_backoff_spec
#
# PROOF: the first wait computes; a later one caps the same doubled wait
# the same way (gbs.cap: case by case).

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_backoff.bend as GatewayBackoff

def gbs.cap(b: Bool, x: Nat) -> {Gb.next.cap(b, x) == GatewayBackoff.gb_cap(b, x) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def GatewayBackoff.gateway_backoff_spec(m):
  match m:
    case None{}:
      {==}
    case Some{+d}:
      gbs.cap(Nat.is_le(Nat.mul(2n, d), 10000n), Nat.mul(2n, d))
