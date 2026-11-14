# eukhe: the proof of LAW server_peer_entry_exact
#
# PROOF: the Nat decoder answers Got{n, rest} only for the spelling of n
# before rest, with n within the wire (spb.nat: wire_nat_exact,
# wire_nat_decoded_fits). The request's decoder reads four Nats in turn,
# so a request it reads is the four spellings before what it leaves
# (spx.peer down to spx.rec); the entry answers a verdict only for a
# request read with nothing left (spx.top).

import Base
import ../../bend/ffi_server_peer.bend as FSp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/server_peer.bend as ServerPeer
import ../base/staging.bend as LStg
import ./base.bend as LA

# what a decode of the request tells: q spelled before r, within the wire
def spx.SP(s: String, d: Wr.Dec<FSp.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ServerPeer.sp_spell(q, r) : String} & {ServerPeer.sp_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the fourth field: the recorded pid
def spx.rec(-s: String, +p: Nat, +o: Nat, +i: Nat, -s3: String, d: Wr.Dec<Nat>, pre: {s == Wr.put_nat(p, Wr.put_nat(o, Wr.put_nat(i, s3))) : String}, hp: {LawsBase.wire_fits(p) == True{} : Bool}, ho: {LawsBase.wire_fits(o) == True{} : Bool}, hi: {LawsBase.wire_fits(i) == True{} : Bool}, nd: LA.spb.NP(s3, d)) -> spx.SP(s, FSp.get_req.rec(p, o, i, d)):
  match d:
    case Wr.Got{+c, +r}:
      match nd:
        case (e, hc):
          +whole = Equal.trans(String, s, Wr.put_nat(p, Wr.put_nat(o, Wr.put_nat(i, s3))), Wr.put_nat(p, Wr.put_nat(o, Wr.put_nat(i, Wr.put_nat(c, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(p, Wr.put_nat(o, Wr.put_nat(i, z))), s3, Wr.put_nat(c, r), e))
          +f3 = LA.spb.and_i(LawsBase.wire_fits(i), LawsBase.wire_fits(c), hi, hc)
          +f2 = LA.spb.and_i(LawsBase.wire_fits(o), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(c)), ho, f3)
          (whole, LA.spb.and_i(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(o), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(c))), hp, f2))
    case Wr.Bad{}:
      Unit{}

# the third field: the listener's pid
def spx.pid(-s: String, +p: Nat, +o: Nat, -s2: String, d: Wr.Dec<Nat>, pre: {s == Wr.put_nat(p, Wr.put_nat(o, s2)) : String}, hp: {LawsBase.wire_fits(p) == True{} : Bool}, ho: {LawsBase.wire_fits(o) == True{} : Bool}, nd: LA.spb.NP(s2, d)) -> spx.SP(s, FSp.get_req.pid(p, o, d)):
  match d:
    case Wr.Got{+i, +s3}:
      match nd:
        case (e, hi):
          +next = Equal.trans(String, s, Wr.put_nat(p, Wr.put_nat(o, s2)), Wr.put_nat(p, Wr.put_nat(o, Wr.put_nat(i, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(p, Wr.put_nat(o, z)), s2, Wr.put_nat(i, s3), e))
          spx.rec(s, p, o, i, s3, Wr.get_nat(s3), next, hp, ho, hi, LA.spb.nat(s3))
    case Wr.Bad{}:
      Unit{}

# the second field: the client's uid
def spx.own(-s: String, +p: Nat, -s1: String, d: Wr.Dec<Nat>, pre: {s == Wr.put_nat(p, s1) : String}, hp: {LawsBase.wire_fits(p) == True{} : Bool}, nd: LA.spb.NP(s1, d)) -> spx.SP(s, FSp.get_req.own(p, d)):
  match d:
    case Wr.Got{+o, +s2}:
      match nd:
        case (e, ho):
          +next = Equal.trans(String, s, Wr.put_nat(p, s1), Wr.put_nat(p, Wr.put_nat(o, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(p, z), s1, Wr.put_nat(o, s2), e))
          spx.pid(s, p, o, s2, Wr.get_nat(s2), next, hp, ho, LA.spb.nat(s2))
    case Wr.Bad{}:
      Unit{}

# the first field: the listener's uid
def spx.peer(+s: String, d: Wr.Dec<Nat>, nd: LA.spb.NP(s, d)) -> spx.SP(s, FSp.get_req.peer(d)):
  match d:
    case Wr.Got{+p, +s1}:
      match nd:
        case (e, hp):
          spx.own(s, p, s1, Wr.get_nat(s1), e, hp, LA.spb.nat(s1))
    case Wr.Bad{}:
      Unit{}

# a verdict answered: a request read whole, nothing left
def spx.top(-s: String, d: Wr.Dec<FSp.Req>, sp: spx.SP(s, d), ok: {LawsBase.wire_opens_err(FSp.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FSp.Req, q => {s == ServerPeer.sp_spell(q, "") : String} & {ServerPeer.sp_fits(q) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, sp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FSp.Req, q2 => {s == ServerPeer.sp_spell(q2, "") : String} & {ServerPeer.sp_fits(q2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FSp.Req, q2 => {s == ServerPeer.sp_spell(q2, "") : String} & {ServerPeer.sp_fits(q2) == True{} : Bool}>, ok)

def ServerPeer.server_peer_entry_exact(s, ok):
  spx.top(s, FSp.get_req(s), spx.peer(s, Wr.get_nat(s), LA.spb.nat(s)), ok)
