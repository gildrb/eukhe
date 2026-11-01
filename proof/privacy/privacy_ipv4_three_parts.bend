# eukhe: the proof of LAW privacy_ipv4_three_parts
#
# PROOF: the IPv4 grammar reads the three octets (LQd.pqd.oct_read), then
# asks for a `.` where t starts with none (p3.quad); the IPv6 reader reads
# the first octet as a group, meets its `.` and asks the same grammar
# (p3.v6).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../spec/harness/privacy.bend as S
import ./base/chars.bend as LIp
import ./base/read.bend as LRd
import ./base/quad.bend as LQd
import ./base/none.bend as LNn
import ../../laws/privacy/ip.bend as PrivacyIp

# three octets, then t: no quad
def p3.quad(+x: String, +y: String, +z: String, +t: String, +hx: {S.octet(x) == True{} : Bool}, +hy: {S.octet(y) == True{} : Bool}, +hz: {S.octet(z) == True{} : Bool}, +ht: {S.stops6(t) == True{} : Bool}) -> {Ip.quad(Ip.Sym.list(String.append(x, SCon{'.', String.append(y, SCon{'.', String.append(z, t)})}))) == None{} : Maybe<&2, Ip.QCut>}:
  +Y1 = String.append(y, SCon{'.', String.append(z, t)})
  +Y2 = String.append(z, t)
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(x, SCon{'.', Y1})), List.append(&2, Ip.Sym, Ip.Sym.list(x), Ip.Sym.list(SCon{'.', Y1})), LRd.prd.sym_app(x, SCon{'.', Y1})) : {Ip.quad.a(Ip.oct(_)) == None{} : Maybe<&2, Ip.QCut>}
  %Equal.sym(Maybe<&2, Ip.Cut>, Ip.oct(List.append(&2, Ip.Sym, Ip.Sym.list(x), Ip.Sym.list(SCon{'.', Y1}))), Some{Ip.Cut{x, Ip.Sym.list(SCon{'.', Y1})}}, LQd.pqd.oct_read(x, Ip.Sym.list(SCon{'.', Y1}), hx, {==})) : {Ip.quad.a(_) == None{} : Maybe<&2, Ip.QCut>}
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(Y1), List.append(&2, Ip.Sym, Ip.Sym.list(y), Ip.Sym.list(SCon{'.', Y2})), LRd.prd.sym_app(y, SCon{'.', Y2})) : {Ip.quad.b(x, Ip.oct(_)) == None{} : Maybe<&2, Ip.QCut>}
  %Equal.sym(Maybe<&2, Ip.Cut>, Ip.oct(List.append(&2, Ip.Sym, Ip.Sym.list(y), Ip.Sym.list(SCon{'.', Y2}))), Some{Ip.Cut{y, Ip.Sym.list(SCon{'.', Y2})}}, LQd.pqd.oct_read(y, Ip.Sym.list(SCon{'.', Y2}), hy, {==})) : {Ip.quad.b(x, _) == None{} : Maybe<&2, Ip.QCut>}
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(Y2), List.append(&2, Ip.Sym, Ip.Sym.list(z), Ip.Sym.list(t)), LRd.prd.sym_app(z, t)) : {Ip.quad.c(x, y, Ip.oct(_)) == None{} : Maybe<&2, Ip.QCut>}
  %Equal.sym(Maybe<&2, Ip.Cut>, Ip.oct(List.append(&2, Ip.Sym, Ip.Sym.list(z), Ip.Sym.list(t))), Some{Ip.Cut{z, Ip.Sym.list(t)}}, LQd.pqd.oct_read(z, Ip.Sym.list(t), hz, LRd.prd.drun_end4(t, LRd.prd.stops6_4(t, ht)))) : {Ip.quad.c(x, y, _) == None{} : Maybe<&2, Ip.QCut>}
  %Equal.sym(Maybe<&2, Ip.Cut>, Ip.dot_oct(Ip.Sym.list(t)), None{}, LNn.pnn.dot(Ip.Sym.list(t), LNn.pnn.stop_nodot(t, ht))) : {Ip.quad.d(x, y, z, _) == None{} : Maybe<&2, Ip.QCut>}
  {==}

# the IPv6 reader meets the first `.` inside its first group and asks the
# IPv4 grammar from the group's start
def p3.v6(b: Bool, +x: String, +Y: String, +hx: {S.octet(x) == True{} : Bool}, +hq: {Ip.quad(Ip.Sym.list(String.append(x, SCon{'.', Y}))) == None{} : Maybe<&2, Ip.QCut>}) -> {Ip.v6.go(b, String.append(x, SCon{'.', Y})) == None{} : Maybe<&2, Nat>}:
  match b:
    case False{}:
      {==}
    case True{}:
      +X = String.append(x, SCon{'.', Y})
      +D = Ip.Sym.list(SCon{'.', Y})
      +st = List.append(&2, Ip.Sym, Ip.Sym.list(x), D)
      +hg = LQd.pqd.f_grp(x, LQd.pqd.facts(x, hx))
      %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(X), st, LRd.prd.sym_app(x, SCon{'.', Y})) : {Ip.v6.got(List.length(&2, Ip.Sym, Ip.Sym.list(X)), Ip.read(_, Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}})) == None{} : Maybe<&2, Nat>}
      %Equal.sym(Ip.Read, Ip.read(st, Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}), Ip.read(D, Ip.Grp{st, LRd.prd.room(x)}, Ip.Acc{False{}, Nil{}, Nil{}}), LRd.prd.group_begin(x, D, Ip.Acc{False{}, Nil{}, Nil{}}, hg)) : {Ip.v6.got(List.length(&2, Ip.Sym, Ip.Sym.list(X)), _) == None{} : Maybe<&2, Nat>}
      %LRd.prd.sym_app(x, SCon{'.', Y}) : {Ip.v6.got(List.length(&2, Ip.Sym, Ip.Sym.list(X)), Ip.quad_end(Ip.Acc{False{}, Nil{}, Nil{}}, Ip.quad(_))) == None{} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Ip.QCut>, Ip.quad(Ip.Sym.list(X)), None{}, hq) : {Ip.v6.got(List.length(&2, Ip.Sym, Ip.Sym.list(X)), Ip.quad_end(Ip.Acc{False{}, Nil{}, Nil{}}, _)) == None{} : Maybe<&2, Nat>}
      {==}

def PrivacyIp.privacy_ipv4_three_parts(x, y, z, before, t, ok, nd):
  +hx = LIp.pip.and_l(S.octet(x), Bool.and(S.octet(y), S.octet(z)), ok)
  +hyz = LIp.pip.and_r(S.octet(x), Bool.and(S.octet(y), S.octet(z)), ok)
  +hy = LIp.pip.and_l(S.octet(y), S.octet(z), hyz)
  +hz = LIp.pip.and_r(S.octet(y), S.octet(z), hyz)
  +ht = LNn.pnn.free_stop(t, nd)
  +Y = String.append(y, SCon{'.', String.append(z, t)})
  +X = String.append(x, SCon{'.', Y})
  +hq = p3.quad(x, y, z, t, hx, hy, hz, ht)
  %Equal.sym(Maybe<&2, Nat>, Ip.v6.go(Ip.edge6(Ip.last(before)), X), None{}, p3.v6(Ip.edge6(Ip.last(before)), x, Y, hx, hq)) : {Maybe.or(&2, Nat, _, Ip.v4(before, X)) == None{} : Maybe<&2, Nat>}
  LNn.pnn.v4_at(before, X, hq)
