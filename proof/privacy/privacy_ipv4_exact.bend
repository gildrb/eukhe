# eukhe: the proof of LAW privacy_ipv4_exact
#
# PROOF: what the IPv4 grammar reads is four octets the spec writes,
# followed by a text t that starts with no decimal digit (pqi.quad: each
# char's symbol says what the char is, LCl.pcl.of); the grammar decides on
# that text as the spec does (pd4.decides), so the spec takes it with the
# grammar's length.

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/privacy/context.bend as Cx
import ../../spec/harness/privacy.bend as S
import ./base/chars.bend as LIp
import ./base/v4.bend as LV4
import ./base/qinv.bend as LQi
import ../../laws/privacy/ip.bend as PrivacyIp

# what the law asks for
def pv4x.G(before: String, s: String, n: Nat) -> Type:
  Sigma<&1, &1, Ip.Quad, q => Sigma<&1, &1, String, t => {s == S.quad_text(q, t) : String} & ({S.quad_ok(q) == True{} : Bool} & ({S.stops4(t) == True{} : Bool} & {S.take4(q, before, t, Cx.vctx(before)) == Some{n} : Maybe<&2, Nat>}))>>

def pv4x.IfS(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# none is no answer
def pv4x.none_some(-n: Nat, -G: Type, e: {None{} == Some{n} : Maybe<&2, Nat>}) -> G:
  %e : pv4x.IfS(_, G)
  Unit{}

def pv4x.got(+before: String, +s: String, +n: Nat, m: Maybe<&2, Ip.QCut>, qp: LQi.pqi.QP(s, m), hb: {Ip.v4.got(List.length(&2, Ip.Sym, Ip.Sym.list(s)), m) == Some{n} : Maybe<&2, Nat>}, +h: {Ip.v4(before, s) == Some{n} : Maybe<&2, Nat>}) -> pv4x.G(before, s, n):
  match m:
    case None{}:
      pv4x.none_some(n, pv4x.G(before, s, n), hb)
    case Some{r}:
      match r:
        case Ip.QCut{+q, rest}:
          (+t, pr) = qp
          (+e1, more) = pr
          (e2, ee) = more
          (+e3, f4) = ee
          +e4 = {f4 : {S.stops4(t) == True{} : Bool}}
          +qt = S.quad_text(q, t)
          +V = Equal.trans(Maybe<&2, Nat>, Ip.v4(before, qt), Ip.v4(before, s), Some{n}, Equal.cong(String, Maybe<&2, Nat>, z => Ip.v4(before, z), qt, s, Equal.sym(String, s, qt, e1)), h)
          +TK = Equal.trans(Maybe<&2, Nat>, S.take4(q, before, t, Cx.vctx(before)), Ip.v4(before, qt), Some{n}, Equal.sym(Maybe<&2, Nat>, Ip.v4(before, qt), S.take4(q, before, t, Cx.vctx(before)), LV4.pd4.decides(q, before, t, e3, e4)), V)
          (q, (t, (e1, (e3, (e4, TK)))))

def pv4x.go(b: Bool, +before: String, +s: String, +n: Nat, hb: {Ip.v4.go(b, s) == Some{n} : Maybe<&2, Nat>}, +h: {Ip.v4(before, s) == Some{n} : Maybe<&2, Nat>}) -> pv4x.G(before, s, n):
  match b:
    case False{}:
      pv4x.none_some(n, pv4x.G(before, s, n), hb)
    case True{}:
      pv4x.got(before, s, n, Ip.quad(Ip.Sym.list(s)), LQi.pqi.quad(s), hb, h)

def PrivacyIp.privacy_ipv4_exact(before, s, n, h):
  pv4x.go(Bool.and(Ip.edge4(Ip.last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), before, s, n, h, h)
