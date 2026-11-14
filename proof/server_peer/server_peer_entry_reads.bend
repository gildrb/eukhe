# eukhe: the proof of LAW server_peer_entry_reads
#
# PROOF: each of the four fields is the wire's Nat decoder on its own
# spelling (wire_nat_round_trip, each Nat within the wire), in the order
# Rust spells them; the last leaves rest.

import Base
import ../../bend/ffi_server_peer.bend as FSp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/server_peer.bend as ServerPeer
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ./base.bend as LA

# the decode of n spelled before r, turned around
def spr.back(+n: Nat, +r: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, r} == Wr.get_nat(Wr.put_nat(n, r)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), Wr.Got{n, r}, Wire.wire_nat_round_trip(n, r, h))

def spr.reads(+p: Nat, +o: Nat, +i: Nat, +c: Nat, +rest: String, hp: {LawsBase.wire_fits(p) == True{} : Bool}, ho: {LawsBase.wire_fits(o) == True{} : Bool}, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hc: {LawsBase.wire_fits(c) == True{} : Bool}) -> {FSp.get_req(Wr.put_nat(p, Wr.put_nat(o, Wr.put_nat(i, Wr.put_nat(c, rest))))) == Wr.Got{FSp.Req{p, o, i, c}, rest} : Wr.Dec<FSp.Req>}:
  %spr.back(p, Wr.put_nat(o, Wr.put_nat(i, Wr.put_nat(c, rest))), hp) : {FSp.get_req.peer(_) == Wr.Got{FSp.Req{p, o, i, c}, rest} : Wr.Dec<FSp.Req>}
  %spr.back(o, Wr.put_nat(i, Wr.put_nat(c, rest)), ho) : {FSp.get_req.own(p, _) == Wr.Got{FSp.Req{p, o, i, c}, rest} : Wr.Dec<FSp.Req>}
  %spr.back(i, Wr.put_nat(c, rest), hi) : {FSp.get_req.pid(p, o, _) == Wr.Got{FSp.Req{p, o, i, c}, rest} : Wr.Dec<FSp.Req>}
  %spr.back(c, rest, hc) : {FSp.get_req.rec(p, o, i, _) == Wr.Got{FSp.Req{p, o, i, c}, rest} : Wr.Dec<FSp.Req>}
  {==}

def spr.req(q: FSp.Req, +rest: String, +h: {ServerPeer.sp_fits(q) == True{} : Bool}) -> {FSp.get_req(ServerPeer.sp_spell(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSp.Req>}:
  match q:
    case FSp.Req{+p, +o, +i, +c}:
      +h1 = LA.spb.and_r(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(o), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(c))), h)
      +h2 = LA.spb.and_r(LawsBase.wire_fits(o), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(c)), h1)
      +h3 = LA.spb.and_r(LawsBase.wire_fits(i), LawsBase.wire_fits(c), h2)
      spr.reads(p, o, i, c, rest, LA.spb.and_l(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(o), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(c))), h), LA.spb.and_l(LawsBase.wire_fits(o), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(c)), h1), LA.spb.and_l(LawsBase.wire_fits(i), LawsBase.wire_fits(c), h2), h3)

def ServerPeer.server_peer_entry_reads(q, rest, h):
  spr.req(q, rest, h)
