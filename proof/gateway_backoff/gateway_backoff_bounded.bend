# eukhe: the proof of LAW gateway_backoff_bounded
#
# PROOF: the first wait is 250; a later one is the doubled wait only when
# that is at most 10000 (gbb.cap), else 10000.

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_backoff.bend as GatewayBackoff

def gbb.cap(b: Bool, x: Nat, eb: {Nat.is_le(x, 10000n) == b : Bool}) -> {Nat.is_le(Gb.next.cap(b, x), 10000n) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      {==}

def GatewayBackoff.gateway_backoff_bounded(m):
  match m:
    case None{}:
      {==}
    case Some{+d}:
      gbb.cap(Nat.is_le(Nat.mul(2n, d), 10000n), Nat.mul(2n, d), {==})
