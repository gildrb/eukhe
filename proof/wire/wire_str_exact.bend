# eukhe: the proof of LAW wire_str_exact

import Base
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../base/logic/string.bend as LLogicString
import ../base/logic/wire.bend as LLogicWire
import ../base/wire.bend as LWire
import ./wire_nat_exact.bend as PWireNatExact

# what take's answer says about its input s
def wr_pt(s: String, n: Nat, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+a, r}:
      {s == LLogicString.wr_app(a, r) : String} & {String.length(a) == n : Nat}
    case Wr.Bad{}:
      Unit

def wr_take_step(c: Char, +t: String, -m: Nat, r: Wr.Dec<String>, ih: wr_pt(t, m, r)) ->
  wr_pt(SCon{c, t}, 1n+m, LLogicWire.wo_take_cons(c, r)):
  match r:
    case Wr.Got{+a, +s3}:
      (e1, e2) = ih
      (Equal.cong(String, String, z => SCon{c, z}, t, LLogicString.wr_app(a, s3), e1),
        Equal.cong(Nat, Nat, k => 1n+k, String.length(a), m, e2))
    case Wr.Bad{}:
      Unit{}

# the reference take(n, s) == Got{a, r} only when s == a ++ r and a has n chars
def wr_take_spec(n: Nat, s: String) -> wr_pt(s, n, LLogicWire.wo_take(n, s)):
  match n:
    case 0n:
      ({==}, {==})
    case 1n++m:
      match s:
        case SNil{}:
          Unit{}
        case SCon{c, +t}:
          wr_take_step(c, t, m, LLogicWire.wo_take(m, t), wr_take_spec(m, t))

# what a String decoder answer says about its input s
def wr_ps(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String}
    case Wr.Bad{}:
      Unit

def wr_str_conv(+s: String, +s2: String, -n: Nat, en: {s == Wr.put_nat(n, s2) : String},
  d: Wr.Dec<String>, pt: wr_pt(s2, n, d)) -> wr_ps(s, d):
  match d:
    case Wr.Got{+a, +r}:
      (e1, e2) = pt
      %Equal.sym(String, Wr.put_str(a, r), Wr.put_nat(String.length(a), LLogicString.wr_app(a, r)), LWire.wr_put_str(a, r)) : {s == _ : String}
      %Equal.sym(Nat, String.length(a), n, e2) : {s == Wr.put_nat(_, LLogicString.wr_app(a, r)) : String}
      %e1 : {s == Wr.put_nat(n, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def wr_str_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  wr_ps(s, Wr.get_str.go(r)):
  match r:
    case Wr.Got{+n, +s2}:
      %Equal.sym(Wr.Dec<String>, Wr.take(n, s2), LLogicWire.wo_take(n, s2), LWire.wr_take_eq(n, s2)) : wr_ps(s, _)
      wr_str_conv(s, s2, n, Wire.wire_nat_exact(s, n, s2, er), LLogicWire.wo_take(n, s2), wr_take_spec(n, s2))
    case Wr.Bad{}:
      Unit{}

def Wire.wire_str_exact(s, a, rest, h):
  %h : wr_ps(s, _)
  wr_str_top(s, Wr.get_nat(s), {==})
