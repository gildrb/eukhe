# eukhe: the proof of LAW semver_ffi_exact_fits
#
# As semver_ffi_exact, carrying the fits: a decoded string's length fits
# (an encoding whose length does not fit reads as no string:
# wire_nat_too_long), and a decoded list's count is a decoded Nat
# (wire_nat_decoded_fits) equal to its length (the item loop counts it).

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/semver.bend as Semver
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_too_long.bend as PWireNatTooLong
import ../wire/wire_str_exact.bend as PWireStrExact
import ../base/wire.bend as LWire
import ../base/logic/string.bend as LLogicString
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LASemver

def sf.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def sf.DT(d: Wr.Dec<String>, G: Type) -> Type:
  match d:
    case Wr.Got{x, r}:
      Unit
    case Wr.Bad{}:
      G

def sf.got_bad(-G: Type, -x: String, -r: String, e: {Wr.Got{x, r} == Wr.Bad{} : Wr.Dec<String>}) -> G:
  %e : sf.DT(_, G)
  Unit{}

# a decoded string's length fits
def sf.str_fits.at(b: Bool, +s: String, +a: String, +r: String, eb: {LawsBase.wire_fits(String.length(a)) == b : Bool}, e1: {s == Wr.put_str(a, r) : String}, ed: {Wr.get_str(s) == Wr.Got{a, r} : Wr.Dec<String>}) -> {LawsBase.wire_fits(String.length(a)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +x = LLogicString.wr_app(a, r)
      +c1 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(s), Wr.get_str(Wr.put_str(a, r)), Equal.sym(Wr.Dec<String>, Wr.get_str(s), Wr.Got{a, r}, ed), Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), s, Wr.put_str(a, r), e1))
      +c2 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_str(a, r)), Wr.get_str(Wr.put_nat(String.length(a), x)), c1, Equal.cong(String, Wr.Dec<String>, z => Wr.get_str(z), Wr.put_str(a, r), Wr.put_nat(String.length(a), x), LWire.wr_put_str(a, r)))
      +c3 = Equal.trans(Wr.Dec<String>, Wr.Got{a, r}, Wr.get_str(Wr.put_nat(String.length(a), x)), Wr.Bad{}, c2, Equal.cong(Wr.Dec<Nat>, Wr.Dec<String>, z => Wr.get_str.go(z), Wr.get_nat(Wr.put_nat(String.length(a), x)), Wr.Bad{}, Wire.wire_nat_too_long(String.length(a), x, eb)))
      sf.got_bad({LawsBase.wire_fits(String.length(a)) == True{} : Bool}, a, r, c3)

def sf.SP(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sf.str.at(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> sf.SP(s, d):
  match d:
    case Wr.Got{+a, +r}:
      +e2 = ed
      +e1 = Wire.wire_str_exact(s, a, r, e2)
      (e1, sf.str_fits.at(LawsBase.wire_fits(String.length(a)), s, a, r, {==}, e1, e2))
    case Wr.Bad{}:
      Unit{}

def sf.str(+s: String) -> sf.SP(s, Wr.get_str(s)):
  sf.str.at(s, Wr.get_str(s), {==})

def sf.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sf.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> sf.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def sf.nat(+s: String) -> sf.NP(s, Wr.get_nat(s)):
  sf.nat.at(s, Wr.get_nat(s), {==})

# Lists of strings
# ----------------

def sf.PL(s: String, m: Nat, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      ({s == LASemver.sv_ss_items(xs, r) : String} & {List.length(&2, String, xs) == 1n+m : Nat}) & {Semver.strs_all(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sf.step(-s: String, +x: String, +s3: String, -k: Nat, ex1: {s == Wr.put_str(x, s3) : String}, fx: {LawsBase.wire_fits(String.length(x)) == True{} : Bool},
  d: Wr.Dec<List<&2, String>>, ih: sf.PL(s3, k, d)) -> sf.PL(s, 1n+k, Wr.get_list.cons(String, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (h, fa) = ih
      (e1, e2) = h
      ((Equal.trans(String, s, Wr.put_str(x, s3), Wr.put_str(x, LASemver.sv_ss_items(ys, r)), ex1,
          Equal.cong(String, String, z => Wr.put_str(x, z), s3, LASemver.sv_ss_items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, String, ys), 1n+k, e2)),
        sf.and_tt(LawsBase.wire_fits(String.length(x)), Semver.strs_all(ys), fx, fa))
    case Wr.Bad{}:
      Unit{}

def sf.loop(m: Nat, cur: Wr.Dec<String>, +s: String, xp: sf.SP(s, cur)) -> sf.PL(s, m, Wr.get_list.go(~String, ~Wr.get_str, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = xp
      ((e, {==}), sf.and_tt(LawsBase.wire_fits(String.length(x)), True{}, f, {==}))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = xp
      sf.step(s, x, s3, k, e, f, Wr.get_list.go(~String, ~Wr.get_str, k, Wr.get_str(s3)), sf.loop(k, Wr.get_str(s3), s3, sf.str(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def sf.TP(s: String, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Semver.spell_tags(xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), Semver.strs_all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sf.conv2(-s: String, +s2: String, +m: Nat, +xs: List<&2, String>, +r: String, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e1: {s2 == LASemver.sv_ss_items(xs, r) : String}, +e2: {List.length(&2, String, xs) == 1n+m : Nat}, fa: {Semver.strs_all(xs) == True{} : Bool}) ->
  ({s == Semver.spell_tags(xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), Semver.strs_all(xs)) == True{} : Bool}):
  +a1 = Equal.cong(String, String, z => Wr.put_nat(1n+m, z), s2, LASemver.sv_ss_items(xs, r), e1)
  +a2 = Equal.cong(Nat, String, n => Wr.put_nat(n, LASemver.sv_ss_items(xs, r)), 1n+m, List.length(&2, String, xs), Equal.sym(Nat, List.length(&2, String, xs), 1n+m, e2))
  +a3 = Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, xs, r), Wr.put_nat(List.length(&2, String, xs), LASemver.sv_ss_items(xs, r)), LASemver.sv_ss_put(xs, r))
  (Equal.trans(String, s, Wr.put_nat(1n+m, s2), Wr.put_list(~String, ~Wr.put_str, xs, r), en,
    Equal.trans(String, Wr.put_nat(1n+m, s2), Wr.put_nat(1n+m, LASemver.sv_ss_items(xs, r)), Wr.put_list(~String, ~Wr.put_str, xs, r), a1,
      Equal.trans(String, Wr.put_nat(1n+m, LASemver.sv_ss_items(xs, r)), Wr.put_nat(List.length(&2, String, xs), LASemver.sv_ss_items(xs, r)), Wr.put_list(~String, ~Wr.put_str, xs, r), a2, a3))),
   sf.and_tt(LawsBase.wire_fits(List.length(&2, String, xs)), Semver.strs_all(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, String, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, n => LawsBase.wire_fits(n), List.length(&2, String, xs), 1n+m, e2), fm), fa))

def sf.conv(-s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fm: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, String>>, pl: sf.PL(s2, m, d)) -> sf.TP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (h, fa) = pl
      (e1, e2) = h
      sf.conv2(s, s2, m, xs, r, en, fm, e1, e2, fa)
    case Wr.Bad{}:
      Unit{}

def sf.lnat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> sf.TP(s, Wr.get_list.start(~String, ~Wr.get_str, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      sf.conv(s, s2, m, en, fn, Wr.get_list.go(~String, ~Wr.get_str, m, Wr.get_str(s2)), sf.loop(m, Wr.get_str(s2), s2, sf.str(s2)))

def sf.ltop(-s: String, d: Wr.Dec<Nat>, np: sf.NP(s, d)) -> sf.TP(s, Wr.get_list.start(~String, ~Wr.get_str, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e, f) = np
      sf.lnat(s, n, s2, e, f)
    case Wr.Bad{}:
      Unit{}

def sf.tags(+s: String) -> sf.TP(s, Wr.get_list(~String, ~Wr.get_str, s)):
  sf.ltop(s, Wr.get_nat(s), sf.nat(s))

# The request
# -----------

# a request spelled before rest
def sf.spell(q: FSv.Req, rest: String) -> String:
  match q:
    case FSv.QRelease{c, ts}:
      Wr.put_nat(0n, Wr.put_str(c, Semver.spell_tags(ts, rest)))
    case FSv.QSeries{w, r}:
      Wr.put_nat(1n, Wr.put_str(w, Wr.put_str(r, rest)))

def sf.RP(s: String, d: Wr.Dec<FSv.Req>) -> Type:
  match d:
    case Wr.Got{q, rest}:
      {s == sf.spell(q, rest) : String} & {Semver.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sf.after(-s: String, +t: Nat, -s1: String, -x: String, pre: {s == Wr.put_nat(t, s1) : String}, e: {s1 == x : String}) -> {s == Wr.put_nat(t, x) : String}:
  Equal.trans(String, s, Wr.put_nat(t, s1), Wr.put_nat(t, x), pre, Equal.cong(String, String, z => Wr.put_nat(t, z), s1, x, e))

def sf.rel.tags(-s: String, +c: String, -s2: String, pre: {s == Wr.put_nat(0n, Wr.put_str(c, s2)) : String}, fc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, tp: sf.TP(s2, d)) -> sf.RP(s, FSv.get_release.tags(c, d)):
  match d:
    case Wr.Got{+ts, +r}:
      (e, f) = tp
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_str(c, s2)), Wr.put_nat(0n, Wr.put_str(c, Semver.spell_tags(ts, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_str(c, z)), s2, Semver.spell_tags(ts, r), e)),
        sf.and_tt(LawsBase.wire_fits(String.length(c)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ts)), Semver.strs_all(ts)), fc, f))
    case Wr.Bad{}:
      Unit{}

def sf.rel(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, sp: sf.SP(s1, d)) -> sf.RP(s, FSv.get_release(d)):
  match d:
    case Wr.Got{+c, +s2}:
      (e, fc) = sp
      sf.rel.tags(s, c, s2, sf.after(s, 0n, s1, Wr.put_str(c, s2), pre, e), fc, Wr.get_list(~String, ~Wr.get_str, s2), sf.tags(s2))
    case Wr.Bad{}:
      Unit{}

def sf.ser.r(-s: String, +w: String, -s2: String, pre: {s == Wr.put_nat(1n, Wr.put_str(w, s2)) : String}, fw: {LawsBase.wire_fits(String.length(w)) == True{} : Bool}, d: Wr.Dec<String>, sp: sf.SP(s2, d)) -> sf.RP(s, FSv.get_series.release(w, d)):
  match d:
    case Wr.Got{+r, +s3}:
      (e, fr) = sp
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_str(w, s2)), Wr.put_nat(1n, Wr.put_str(w, Wr.put_str(r, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(w, z)), s2, Wr.put_str(r, s3), e)),
        sf.and_tt(LawsBase.wire_fits(String.length(w)), LawsBase.wire_fits(String.length(r)), fw, fr))
    case Wr.Bad{}:
      Unit{}

def sf.ser(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: sf.SP(s1, d)) -> sf.RP(s, FSv.get_series(d)):
  match d:
    case Wr.Got{+w, +s2}:
      (e, fw) = sp
      sf.ser.r(s, w, s2, sf.after(s, 1n, s1, Wr.put_str(w, s2), pre, e), fw, Wr.get_str(s2), sf.str(s2))
    case Wr.Bad{}:
      Unit{}

def sf.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> sf.RP(s, FSv.get_req.tag(t, s1)):
  match t:
    case 0n:
      sf.rel(s, s1, pre, Wr.get_str(s1), sf.str(s1))
    case 1n:
      sf.ser(s, s1, pre, Wr.get_str(s1), sf.str(s1))
    case 2n+u:
      Unit{}

def sf.go(-s: String, d: Wr.Dec<Nat>, np: sf.NP(s, d)) -> sf.RP(s, FSv.get_req.start(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      sf.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def sf.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  LLogicLogic.pt.absurd(G, e)

def sf.top.spell(-s: String, q: FSv.Req, rp: ({s == sf.spell(q, "") : String} & {Semver.req_fits(q) == True{} : Bool})) -> ({s == Semver.spell_req(q) : String} & {Semver.req_fits(q) == True{} : Bool}):
  match q:
    case FSv.QRelease{c, ts}:
      rp
    case FSv.QSeries{w, r}:
      rp

def sf.top(-s: String, d: Wr.Dec<FSv.Req>, rp: sf.RP(s, d), ok: {LawsBase.wire_opens_err(FSv.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String} & {Semver.req_fits(q) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, sf.top.spell(s, q, rp))
        case SCon{x, y}:
          sf.tf(Sigma<&1, &1, FSv.Req, q2 => {s == Semver.spell_req(q2) : String} & {Semver.req_fits(q2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      sf.tf(Sigma<&1, &1, FSv.Req, q2 => {s == Semver.spell_req(q2) : String} & {Semver.req_fits(q2) == True{} : Bool}>, ok)

def Semver.semver_ffi_exact_fits(s, ok):
  sf.top(s, FSv.get_req(s), sf.go(s, Wr.get_nat(s), sf.nat(s)), ok)
