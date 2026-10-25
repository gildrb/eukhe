# eukhe: the proof of LAW gateway_backoff_example
#
# PROOF: closed. Each doubled wait the cap keeps (500, 1000, 8000, 10000)
# is rewritten to its literal by gbe.next_is, whose premise Nat.is_eq
# computes; then both sides compute. A bare `{==}` would compare each
# doubled wait with its literal one successor at a time, a recursion as
# deep as the number (10000 frames): near the default machine stack.

import Base
import ../../bend/gateway_backoff.bend as Gb
import ../../bend/ffi_gateway_backoff.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_backoff.bend as GatewayBackoff
import ../base/logic/nat.bend as LLogicNat

# the wait after d is w, when Nat.is_eq says so
def gbe.next_is(d: Nat, w: Nat, h: {Nat.is_eq(w, Gb.next(Some{d})) == True{} : Bool}) -> {w == Gb.next(Some{d}) : Nat}:
  LLogicNat.pq.eq_true(w, Gb.next(Some{d}), h)

def GatewayBackoff.gateway_backoff_example():
  %gbe.next_is(250n, 500n, {==}) : {[Gb.next(None{}), _, Gb.next(Some{500n}), Gb.next(Some{4000n}), Gb.next(Some{5000n}), Gb.next(Some{8000n}), Gb.next(Some{10000n})] == [250n, 500n, 1000n, 8000n, 10000n, 10000n, 10000n] : List<&2, Nat>}
  %gbe.next_is(500n, 1000n, {==}) : {[Gb.next(None{}), 500n, _, Gb.next(Some{4000n}), Gb.next(Some{5000n}), Gb.next(Some{8000n}), Gb.next(Some{10000n})] == [250n, 500n, 1000n, 8000n, 10000n, 10000n, 10000n] : List<&2, Nat>}
  %gbe.next_is(4000n, 8000n, {==}) : {[Gb.next(None{}), 500n, 1000n, _, Gb.next(Some{5000n}), Gb.next(Some{8000n}), Gb.next(Some{10000n})] == [250n, 500n, 1000n, 8000n, 10000n, 10000n, 10000n] : List<&2, Nat>}
  %gbe.next_is(5000n, 10000n, {==}) : {[Gb.next(None{}), 500n, 1000n, 8000n, _, Gb.next(Some{8000n}), Gb.next(Some{10000n})] == [250n, 500n, 1000n, 8000n, 10000n, 10000n, 10000n] : List<&2, Nat>}
  {==}
