# eukhe: the proof of LAW privacy_ipv6_exact
#
# PROOF: every answer of the reader is a shaped address the spec writes,
# then the rest of the text (pri.rd: by induction on the text left, with
# what the reader has read so far as the spec's text, pri.Inv); the reader
# takes it only when no word char, `:` or `.` follows, so the rest stops
# an IPv6 (pv6x.after); the reader decides on that text as the spec does
# (pdc.decides), so the spec takes it with the reader's length.

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../spec/harness/privacy.bend as S
import ./base/chars.bend as LIp
import ./base/decide.bend as LDc
import ./base/none.bend as LNn
import ./base/rinv.bend as LRi
import ./base/rstep.bend as LRs
import ../../laws/privacy/ip.bend as PrivacyIp

# what the law asks for
def pv6x.G(before: String, s: String, n: Nat) -> Type:
  Sigma<&1, &1, Ip.Addr, a => Sigma<&1, &1, String, t => {s == S.text6(a, t) : String} & ({S.shaped(a) == True{} : Bool} & ({S.stops6(t) == True{} : Bool} & {S.take6(a, before, t) == Some{n} : Maybe<&2, Nat>}))>>

def pv6x.IfS(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def pv6x.none_some(-n: Nat, -G: Type, e: {None{} == Some{n} : Maybe<&2, Nat>}) -> G:
  %e : pv6x.IfS(_, G)
  Unit{}

# an answer: its test holds
def pv6x.ans_true(b: Bool, -k: Nat, -n: Nat, e: {Ip.ans(b, k) == Some{n} : Maybe<&2, Nat>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pv6x.none_some(n, {False{} == True{} : Bool}, e)

# what follows an answer stops an IPv6
def pv6x.after(+t: String, -rest: List<&2, Ip.Sym>, +e2: {rest == Ip.Sym.list(t) : List<&2, Ip.Sym>}, +h: {Ip.after6(rest) == True{} : Bool}) -> {S.stops6(t) == True{} : Bool}:
  LNn.pnn.free_stop(t, Equal.trans(Bool, S.free(S.first(t)), Ip.after6(Ip.Sym.list(t)), True{}, Equal.sym(Bool, Ip.after6(Ip.Sym.list(t)), S.free(S.first(t)), LDc.pdc.after6(t)), Equal.trans(Bool, Ip.after6(Ip.Sym.list(t)), Ip.after6(rest), True{}, Equal.cong(List<&2, Ip.Sym>, Bool, z => Ip.after6(z), Ip.Sym.list(t), rest, Equal.sym(List<&2, Ip.Sym>, rest, Ip.Sym.list(t), e2)), h)))

def pv6x.got(+before: String, +s: String, +n: Nat, r: Ip.Read, rp: LRi.pri.RP(s, r), hb: {Ip.v6.got(List.length(&2, Ip.Sym, Ip.Sym.list(s)), r) == Some{n} : Maybe<&2, Nat>}, +h: {Ip.v6(before, s) == Some{n} : Maybe<&2, Nat>}) -> pv6x.G(before, s, n):
  match r:
    case Ip.Bad{}:
      pv6x.none_some(n, pv6x.G(before, s, n), hb)
    case Ip.Got{+a, +rest}:
      (+t, pr) = rp
      (+e1, more) = pr
      (+e2, sh0) = more
      +sh = {sh0 : {S.shaped(a) == True{} : Bool}}
      +k = Nat.sub(List.length(&2, Ip.Sym, Ip.Sym.list(s)), List.length(&2, Ip.Sym, rest))
      +hok = pv6x.ans_true(Bool.and(Bool.and(Ip.counted(a), Ip.digit(a)), Ip.after6(rest)), k, n, hb)
      +st = pv6x.after(t, rest, e2, LIp.pip.and_r(Bool.and(Ip.counted(a), Ip.digit(a)), Ip.after6(rest), hok))
      +x6 = S.text6(a, t)
      +V = Equal.trans(Maybe<&2, Nat>, Ip.v6(before, x6), Ip.v6(before, s), Some{n}, Equal.cong(String, Maybe<&2, Nat>, z => Ip.v6(before, z), x6, s, Equal.sym(String, s, x6, e1)), h)
      +TK = Equal.trans(Maybe<&2, Nat>, S.take6(a, before, t), Ip.v6(before, x6), Some{n}, Equal.sym(Maybe<&2, Nat>, Ip.v6(before, x6), S.take6(a, before, t), LDc.pdc.decides(a, before, t, sh, st)), V)
      (a, (t, (e1, (sh, (st, TK)))))

def pv6x.go(b: Bool, +before: String, +s: String, +n: Nat, hb: {Ip.v6.go(b, s) == Some{n} : Maybe<&2, Nat>}, +h: {Ip.v6(before, s) == Some{n} : Maybe<&2, Nat>}) -> pv6x.G(before, s, n):
  match b:
    case False{}:
      pv6x.none_some(n, pv6x.G(before, s, n), hb)
    case True{}:
      +A0 = {Ip.Acc{False{}, Nil{}, Nil{}} : Ip.Acc}
      pv6x.got(before, s, n, Ip.read(Ip.Sym.list(s), Ip.Begin{}, A0), LRs.pri.rd(s, Ip.Begin{}, A0, s, ({==}, {==})), hb, h)

def PrivacyIp.privacy_ipv6_exact(before, s, n, h):
  pv6x.go(Ip.edge6(Ip.last(before)), before, s, n, h, h)
