# eukhe: the proof of LAW tiny_elect_entry_exact
#
# PROOF: each decoder of bend/ffi_tiny_elect.bend answers Got{x, rest}
# only for an input that is the spec's spelling of x before rest, with x
# within the wire (tx.*: a predicate per decoder answer, carried stage by
# stage with the wire's exactness laws wire_nat_exact, wire_str_exact and
# the refusal of a too long count, wire_nat_too_long). The entry answers
# a value only for a request read whole with nothing left: that input is
# the spelled request (tx.top).

import Base
import ../../bend/tiny.bend as Tn
import ../../bend/ffi_tiny_elect.bend as FTe
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny.bend as Tiny
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_too_long.bend as PWireNatTooLong
import ../wire/wire_str_exact.bend as PWireStrExact
import ../base/wire.bend as LWire
import ../base/logic/string.bend as LLogicString
import ./base.bend as LA

# Logic
# -----

def tx.DT(-A: Data, d: Wr.Dec<A>, G: Type) -> Type:
  match d:
    case Wr.Got{x, r}:
      Unit
    case Wr.Bad{}:
      G

# a decoder answered Got and Bad
def tx.got_bad(-A: Data, -G: Type, -x: A, -r: String, e: {Wr.Got{x, r} == Wr.Bad{} : Wr.Dec<A>}) -> G:
  %e : tx.DT(A, _, G)
  Unit{}

# s is the tag t then s1, and s1 is x: s is the tag t then x
def tx.after(-s: String, +t: Nat, -s1: String, -x: String, pre: {s == Wr.put_nat(t, s1) : String}, e: {s1 == x : String}) -> {s == Wr.put_nat(t, x) : String}:
  Equal.trans(String, s, Wr.put_nat(t, s1), Wr.put_nat(t, x), pre, Equal.cong(String, String, z => Wr.put_nat(t, z), s1, x, e))

# Primitives
# ----------

def tx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String}
    case Wr.Bad{}:
      Unit

def tx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_exact(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def tx.nat(+s: String) -> tx.NP(s, Wr.get_nat(s)):
  tx.nat.at(s, Wr.get_nat(s), {==})

# a decoded string's length fits: a longer one's count is refused
def tx.str_fits.at(b: Bool, +s: String, +a: String, +r: String, eb: {LawsBase.wire_fits(String.length(a)) == b : Bool}, e1: {s == Wr.put_str(a, r) : String}, ed: {Wr.get_str(s) == Wr.Got{a, r} : Wr.Dec<String>}) -> {LawsBase.wire_fits(String.length(a)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +x = LLogicString.wr_app(a, r)
      +c1 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(s), Wr.get_str(Wr.put_str(a, r)), Equal.sym(Wr.Dec<String>, Wr.get_str(s), Wr.Got{a, r}, ed), Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), s, Wr.put_str(a, r), e1))
      +c2 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_str(a, r)), Wr.get_str(Wr.put_nat(String.length(a), x)), c1, Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), Wr.put_str(a, r), Wr.put_nat(String.length(a), x), LWire.wr_put_str(a, r)))
      +c3 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_nat(String.length(a), x)), Wr.Bad{}, c2, Equal.cong(Wr.Dec<Nat>, Wr.Dec<String>, z => Wr.get_str.go(z), Wr.get_nat(Wr.put_nat(String.length(a), x)), Wr.Bad{}, Wire.wire_nat_too_long(String.length(a), x, eb)))
      tx.got_bad(String, {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, a, r, c3)

def tx.SP(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.str.at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> tx.SP(s, d):
  match d:
    case Wr.Got{+a, +r}:
      +e2 = ed
      +e1 = Wire.wire_str_exact(s, a, r, e2)
      (e1, tx.str_fits.at(LawsBase.wire_fits(String.length(a)), s, a, r, {==}, e1, e2))
    case Wr.Bad{}:
      Unit{}

def tx.str(+s: String) -> tx.SP(s, Wr.get_str(s)):
  tx.str.at(s, Wr.get_str(s), {==})

# Probes
# ------

def tx.PrP(s: String, d: Wr.Dec<Tn.Probe>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == Tiny.sp_w_probe(p, r) : String} & {Tiny.sp_fit_probe(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.probe.pong(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, sp: tx.SP(s1, d)) -> tx.PrP(s, FTe.get_probe.pong(d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = sp
      (tx.after(s, 2n, s1, Wr.put_str(a, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def tx.probe.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.PrP(s, FTe.get_probe.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      (pre, {==})
    case 2n:
      tx.probe.pong(s, s1, pre, Wr.get_str(s1), tx.str(s1))
    case 3n:
      (pre, {==})
    case 4n:
      (pre, {==})
    case 5n:
      (pre, {==})
    case 6n+u:
      Unit{}

def tx.probe.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.PrP(s, FTe.get_probe(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.probe.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.probe(+s: String) -> tx.PrP(s, FTe.get_probe(Wr.get_nat(s))):
  tx.probe.go(s, Wr.get_nat(s), tx.nat(s))

# Heard, Fresh, Launch
# --------------------

def tx.HP(s: String, d: Wr.Dec<Tn.Heard>) -> Type:
  match d:
    case Wr.Got{h, r}:
      {s == Wr.put_nat(Tiny.sp_w_heard(h), r) : String}
    case Wr.Bad{}:
      Unit

def tx.heard.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.HP(s, FTe.get_heard.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n:
      pre
    case 4n+u:
      Unit{}

def tx.heard.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.HP(s, FTe.get_heard(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.heard.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.heard(+s: String) -> tx.HP(s, FTe.get_heard(Wr.get_nat(s))):
  tx.heard.go(s, Wr.get_nat(s), tx.nat(s))

def tx.FP(s: String, d: Wr.Dec<Tn.Fresh>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == Wr.put_nat(Tiny.sp_w_fresh(f), r) : String}
    case Wr.Bad{}:
      Unit

def tx.fresh.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.FP(s, FTe.get_fresh.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n+u:
      Unit{}

def tx.fresh.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.FP(s, FTe.get_fresh(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.fresh.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.fresh(+s: String) -> tx.FP(s, FTe.get_fresh(Wr.get_nat(s))):
  tx.fresh.go(s, Wr.get_nat(s), tx.nat(s))

def tx.LP(s: String, d: Wr.Dec<Tn.Launch>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Wr.put_nat(Tiny.sp_w_launch(l), r) : String}
    case Wr.Bad{}:
      Unit

def tx.launch.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.LP(s, FTe.get_launch.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n+u:
      Unit{}

def tx.launch.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.LP(s, FTe.get_launch(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.launch.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.launch(+s: String) -> tx.LP(s, FTe.get_launch(Wr.get_nat(s))):
  tx.launch.go(s, Wr.get_nat(s), tx.nat(s))

# The request
# -----------

def tx.RP(s: String, d: Wr.Dec<FTe.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Tiny.sp_w_req(q, r) : String} & {Tiny.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the request tag of a probe and a launch tag: elect (c = True), confirm
def tx.pm.k(c: Bool) -> Nat:
  match c:
    case True{}:
      0n
    case False{}:
      3n

def tx.pm.mine(c: Bool, -s: String, +p: Tn.Probe, -s2: String, pre: {s == Wr.put_nat(tx.pm.k(c), Tiny.sp_w_probe(p, s2)) : String}, fp: {Tiny.sp_fit_probe(p) == True{} : Bool}, d: Wr.Dec<String>, sp: tx.SP(s2, d)) -> tx.RP(s, FTe.get_pm.mine(c, p, d)):
  match c:
    case True{}:
      match d:
        case Wr.Got{+a, +r}:
          (e, f) = sp
          (Equal.trans(String, s, Wr.put_nat(0n, Tiny.sp_w_probe(p, s2)), Wr.put_nat(0n, Tiny.sp_w_probe(p, Wr.put_str(a, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Tiny.sp_w_probe(p, z)), s2, Wr.put_str(a, r), e)), LA.te.and_tt(Tiny.sp_fit_probe(p), LawsBase.wire_fits(String.length(a)), fp, f))
        case Wr.Bad{}:
          Unit{}
    case False{}:
      match d:
        case Wr.Got{+a, +r}:
          (e, f) = sp
          (Equal.trans(String, s, Wr.put_nat(3n, Tiny.sp_w_probe(p, s2)), Wr.put_nat(3n, Tiny.sp_w_probe(p, Wr.put_str(a, r))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, Tiny.sp_w_probe(p, z)), s2, Wr.put_str(a, r), e)), LA.te.and_tt(Tiny.sp_fit_probe(p), LawsBase.wire_fits(String.length(a)), fp, f))
        case Wr.Bad{}:
          Unit{}

def tx.pm(+c: Bool, -s: String, -s1: String, pre: {s == Wr.put_nat(tx.pm.k(c), s1) : String}, d: Wr.Dec<Tn.Probe>, pp: tx.PrP(s1, d)) -> tx.RP(s, FTe.get_pm(c, d)):
  match d:
    case Wr.Got{+p, +s2}:
      (e, f) = pp
      tx.pm.mine(c, s, p, s2, tx.after(s, tx.pm.k(c), s1, Tiny.sp_w_probe(p, s2), pre, e), f, Wr.get_str(s2), tx.str(s2))
    case Wr.Bad{}:
      Unit{}

def tx.shut(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Tn.Heard>, hp: tx.HP(s1, d)) -> tx.RP(s, FTe.get_shut(d)):
  match d:
    case Wr.Got{+h, +r}:
      (tx.after(s, 1n, s1, Wr.put_nat(Tiny.sp_w_heard(h), r), pre, hp), {==})
    case Wr.Bad{}:
      Unit{}

def tx.launched.launch(-s: String, +f: Tn.Fresh, -s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(Tiny.sp_w_fresh(f), s2)) : String}, d: Wr.Dec<Tn.Launch>, lp: tx.LP(s2, d)) -> tx.RP(s, FTe.get_launched.launch(f, d)):
  match d:
    case Wr.Got{+l, +r}:
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(Tiny.sp_w_fresh(f), s2)), Wr.put_nat(2n, Wr.put_nat(Tiny.sp_w_fresh(f), Wr.put_nat(Tiny.sp_w_launch(l), r))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(Tiny.sp_w_fresh(f), z)), s2, Wr.put_nat(Tiny.sp_w_launch(l), r), lp)), {==})
    case Wr.Bad{}:
      Unit{}

def tx.launched(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Tn.Fresh>, fp: tx.FP(s1, d)) -> tx.RP(s, FTe.get_launched(d)):
  match d:
    case Wr.Got{+f, +s2}:
      tx.launched.launch(s, f, s2, tx.after(s, 2n, s1, Wr.put_nat(Tiny.sp_w_fresh(f), s2), pre, fp), FTe.get_launch(Wr.get_nat(s2)), tx.launch(s2))
    case Wr.Bad{}:
      Unit{}

def tx.bind(-s: String, -s1: String, pre: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<Tn.Probe>, pp: tx.PrP(s1, d)) -> tx.RP(s, FTe.get_bind(d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, f) = pp
      (tx.after(s, 4n, s1, Tiny.sp_w_probe(p, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def tx.req.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> tx.RP(s, FTe.get_req.tag(t, s1)):
  match t:
    case 0n:
      tx.pm(True{}, s, s1, pre, FTe.get_probe(Wr.get_nat(s1)), tx.probe(s1))
    case 1n:
      tx.shut(s, s1, pre, FTe.get_heard(Wr.get_nat(s1)), tx.heard(s1))
    case 2n:
      tx.launched(s, s1, pre, FTe.get_fresh(Wr.get_nat(s1)), tx.fresh(s1))
    case 3n:
      tx.pm(False{}, s, s1, pre, FTe.get_probe(Wr.get_nat(s1)), tx.probe(s1))
    case 4n:
      tx.bind(s, s1, pre, FTe.get_probe(Wr.get_nat(s1)), tx.probe(s1))
    case 5n+u:
      Unit{}

def tx.req.go(-s: String, d: Wr.Dec<Nat>, np: tx.NP(s, d)) -> tx.RP(s, FTe.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      tx.req.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def tx.req(+s: String) -> tx.RP(s, FTe.get_req(s)):
  tx.req.go(s, Wr.get_nat(s), tx.nat(s))

# a value answered: a request read whole, nothing left
def tx.top(-s: String, d: Wr.Dec<FTe.Req>, rp: tx.RP(s, d), ok: {LawsBase.wire_opens_err(FTe.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FTe.Req, r => {s == Tiny.sp_w_req(r, "") : String} & {Tiny.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LA.te.tf(Sigma<&1, &1, FTe.Req, r2 => {s == Tiny.sp_w_req(r2, "") : String} & {Tiny.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.te.tf(Sigma<&1, &1, FTe.Req, r2 => {s == Tiny.sp_w_req(r2, "") : String} & {Tiny.sp_fit_req(r2) == True{} : Bool}>, ok)

def Tiny.tiny_elect_entry_exact(s, ok):
  tx.top(s, FTe.get_req(s), tx.req(s), ok)
