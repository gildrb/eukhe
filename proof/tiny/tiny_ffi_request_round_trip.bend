# eukhe: the proof of LAW tiny_ffi_request_round_trip

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny.bend as Tiny
import ../../laws/wire.bend as Wire
import ../base.bend as L

# tiny
# ----

def Tiny.tiny_ffi_request_round_trip(chain, up, rest, h0):
  +h = h0
  +hc = L.wr_and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, chain)), LawsBase.wire_nats_fit(chain)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, up)), LawsBase.wire_nats_fit(up)), h)
  +hu = L.wr_and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, chain)), LawsBase.wire_nats_fit(chain)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, up)), LawsBase.wire_nats_fit(up)), h)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, chain, FTn.put_ids(up, rest))), Wr.Got{chain, FTn.put_ids(up, rest)}, Wire.wire_list_round_trip(chain, FTn.put_ids(up, rest), hc)) : {FTn.get_req.chain(_) == Wr.Got{FTn.Req{chain, up}, rest} : Wr.Dec<FTn.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, up, rest)), Wr.Got{up, rest}, Wire.wire_list_round_trip(up, rest, hu)) : {FTn.get_req.up(chain, _) == Wr.Got{FTn.Req{chain, up}, rest} : Wr.Dec<FTn.Req>}
  {==}
