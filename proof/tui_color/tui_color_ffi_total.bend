# eukhe: the proof of LAW tui_color_ffi_total
# Whatever the entry's decoder reads is the spelling of a request whose
# numbers fit, then its rest (tx.req: each number by wire_nat_exact and
# wire_nat_decoded_fits, the stages composed along the request's
# spelling). A decoder that reads nothing, or a rest that is not empty,
# answers the malformed error, which the premise excludes; a request read
# whole is the input's spelling, and its answer is tc_reply (tot.answer:
# the ramp's range test is ramp_in, its rungs the spec's list; the band is
# the model's (FB.fb.band_go), which is omp_level (tui_usage_band_omp);
# the roles are the model's).

import Base
import ../../bend/ffi_tui_color.bend as FTC
import ../../bend/tui_color.bend as TC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tui_color.bend as TuiColor
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ./base.bend as LA
import ./tui_color_ffi_band.bend as FB
import ./tui_usage_band_omp.bend as UO

# Reading
# -------

# s spelled up to a field a is s spelled up to its spelling b
def tx.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# both halves of an and hold
def tx.and(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# a Nat read from s: s is its spelling, then the rest, and it fits
def tx.Nat(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.nat.go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> tx.Nat(s, d):
  match d:
    case Wr.Got{+n, +r}:
      (Wire.wire_nat_exact(s, n, r, ed), Wire.wire_nat_decoded_fits(s, n, r, ed))
    case Wr.Bad{}:
      Unit{}

def tx.nat(+s: String) -> tx.Nat(s, Wr.get_nat(s)):
  tx.nat.go(s, Wr.get_nat(s), {==})

# a color read from s: s is its spelling, then the rest, and it fits
def tx.Px(s: String, d: Wr.Dec<TC.Px>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == TuiColor.spell_px(p, r) : String} & {TuiColor.px_fits(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.px.b(-s: String, +r: Nat, +g: Nat, -s2: String, pre: {s == Wr.put_nat(r, Wr.put_nat(g, s2)) : String}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, fg: {LawsBase.wire_fits(g) == True{} : Bool}, d: Wr.Dec<Nat>, inv: tx.Nat(s2, d)) -> tx.Px(s, FTC.get_px.b(r, g, d)):
  match d:
    case Wr.Got{+b, +s3}:
      (e3, fb) = inv
      (tx.step(z => Wr.put_nat(r, Wr.put_nat(g, z)), s, s2, Wr.put_nat(b, s3), pre, e3), tx.and(LawsBase.wire_fits(r), Bool.and(LawsBase.wire_fits(g), LawsBase.wire_fits(b)), fr, tx.and(LawsBase.wire_fits(g), LawsBase.wire_fits(b), fg, fb)))
    case Wr.Bad{}:
      Unit{}

def tx.px.g(-s: String, +r: Nat, -s1: String, pre: {s == Wr.put_nat(r, s1) : String}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, d: Wr.Dec<Nat>, inv: tx.Nat(s1, d)) -> tx.Px(s, FTC.get_px.g(r, d)):
  match d:
    case Wr.Got{+g, +s2}:
      (e2, fg) = inv
      tx.px.b(s, r, g, s2, tx.step(z => Wr.put_nat(r, z), s, s1, Wr.put_nat(g, s2), pre, e2), fr, fg, Wr.get_nat(s2), tx.nat(s2))
    case Wr.Bad{}:
      Unit{}

def tx.px(-s: String, d: Wr.Dec<Nat>, inv: tx.Nat(s, d)) -> tx.Px(s, FTC.get_px(d)):
  match d:
    case Wr.Got{+r, +s1}:
      (e1, fr) = inv
      tx.px.g(s, r, s1, e1, fr, Wr.get_nat(s1), tx.nat(s1))
    case Wr.Bad{}:
      Unit{}

# a request read from s: s is its spelling, then the rest, and it fits
def tx.Req(s: String, d: Wr.Dec<FTC.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == TuiColor.spell_req(q, r) : String} & {TuiColor.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tx.ramp.n(-s: String, +lo: TC.Px, +hi: TC.Px, -s2: String, pre: {s == Wr.put_nat(0n, TuiColor.spell_px(lo, TuiColor.spell_px(hi, s2))) : String}, flo: {TuiColor.px_fits(lo) == True{} : Bool}, fhi: {TuiColor.px_fits(hi) == True{} : Bool}, d: Wr.Dec<Nat>, inv: tx.Nat(s2, d)) -> tx.Req(s, FTC.get_ramp.n(lo, hi, d)):
  match d:
    case Wr.Got{+n, +s3}:
      (e3, fn) = inv
      (tx.step(z => Wr.put_nat(0n, TuiColor.spell_px(lo, TuiColor.spell_px(hi, z))), s, s2, Wr.put_nat(n, s3), pre, e3), tx.and(TuiColor.px_fits(lo), Bool.and(TuiColor.px_fits(hi), LawsBase.wire_fits(n)), flo, tx.and(TuiColor.px_fits(hi), LawsBase.wire_fits(n), fhi, fn)))
    case Wr.Bad{}:
      Unit{}

def tx.ramp.hi(-s: String, +lo: TC.Px, -s1: String, pre: {s == Wr.put_nat(0n, TuiColor.spell_px(lo, s1)) : String}, flo: {TuiColor.px_fits(lo) == True{} : Bool}, d: Wr.Dec<TC.Px>, inv: tx.Px(s1, d)) -> tx.Req(s, FTC.get_ramp.hi(lo, d)):
  match d:
    case Wr.Got{+hi, +s2}:
      (e2, fhi) = inv
      tx.ramp.n(s, lo, hi, s2, tx.step(z => Wr.put_nat(0n, TuiColor.spell_px(lo, z)), s, s1, TuiColor.spell_px(hi, s2), pre, e2), flo, fhi, Wr.get_nat(s2), tx.nat(s2))
    case Wr.Bad{}:
      Unit{}

def tx.ramp(-s: String, -s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<TC.Px>, inv: tx.Px(s0, d)) -> tx.Req(s, FTC.get_ramp(d)):
  match d:
    case Wr.Got{+lo, +s1}:
      (e1, flo) = inv
      tx.ramp.hi(s, lo, s1, tx.step(z => Wr.put_nat(0n, z), s, s0, TuiColor.spell_px(lo, s1), pre, e1), flo, FTC.get_px(Wr.get_nat(s1)), tx.px(s1, Wr.get_nat(s1), tx.nat(s1)))
    case Wr.Bad{}:
      Unit{}

def tx.band.w(-s: String, +t: Nat, -s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(t, s1)) : String}, ft: {LawsBase.wire_fits(t) == True{} : Bool}, d: Wr.Dec<Nat>, inv: tx.Nat(s1, d)) -> tx.Req(s, FTC.get_band.w(t, d)):
  match d:
    case Wr.Got{+w, +s2}:
      (e2, fw) = inv
      (tx.step(z => Wr.put_nat(1n, Wr.put_nat(t, z)), s, s1, Wr.put_nat(w, s2), pre, e2), tx.and(LawsBase.wire_fits(t), LawsBase.wire_fits(w), ft, fw))
    case Wr.Bad{}:
      Unit{}

def tx.band(-s: String, -s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, inv: tx.Nat(s0, d)) -> tx.Req(s, FTC.get_band(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e1, ft) = inv
      tx.band.w(s, t, s1, tx.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(t, s1), pre, e1), ft, Wr.get_nat(s1), tx.nat(s1))
    case Wr.Bad{}:
      Unit{}

def tx.tag(-s: String, t: Nat, +s0: String, pre: {s == Wr.put_nat(t, s0) : String}) -> tx.Req(s, FTC.get_req.tag(t, s0)):
  match t:
    case 0n:
      tx.ramp(s, s0, pre, FTC.get_px(Wr.get_nat(s0)), tx.px(s0, Wr.get_nat(s0), tx.nat(s0)))
    case 1n:
      tx.band(s, s0, pre, Wr.get_nat(s0), tx.nat(s0))
    case 2n:
      (pre, {==})
    case 3n+p:
      Unit{}

def tx.req.go(+s: String, d: Wr.Dec<Nat>, inv: tx.Nat(s, d)) -> tx.Req(s, FTC.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      (e, f) = inv
      tx.tag(s, t, s0, e)
    case Wr.Bad{}:
      Unit{}

def tx.req(+s: String) -> tx.Req(s, FTC.get_req(s)):
  tx.req.go(s, Wr.get_nat(s), tx.nat(s))

# Answering
# ---------

def tot.ramp(b: Bool, +lo: TC.Px, +hi: TC.Px, +n: Nat) -> {FTC.answer.ramp(b, lo, hi, n) == TuiColor.tc_reply.ramp(b, lo, hi, n) : String}:
  match b:
    case True{}:
      LA.tcf.rungs(TC.ramp(lo, hi, n))
    case False{}:
      {==}

def tot.answer(q: FTC.Req) -> {FTC.answer(q) == TuiColor.tc_reply(q) : String}:
  match q:
    case FTC.QRamp{lo, hi, +n}:
      match lo hi:
        case TC.Px{+lr, +lg, +lb} TC.Px{+hr, +hg, +hb}:
          tot.ramp(TuiColor.ramp_in(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n), TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n)
    case FTC.QBand{+t, +w}:
      %TuiColor.tui_usage_band_omp(t, w) : {Wr.put_nat(FTC.band(t, w), "") == Wr.put_nat(_, "") : String}
      %FB.fb.band_go(TC.bands(), t, w) : {Wr.put_nat(FTC.band.go(TC.bands(), t, w), "") == Wr.put_nat(_, "") : String}
      {==}
    case FTC.QRoles{}:
      {==}

def tot.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FTC.Req, q => {(s, (TuiColor.req_fits(q), a)) == (TuiColor.spell_req(q, ""), (True{}, TuiColor.tc_reply(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def tot.top(+s: String, +q: FTC.Req, +a: String, e: {s == TuiColor.spell_req(q, "") : String}, f: {TuiColor.req_fits(q) == True{} : Bool}, ea: {a == TuiColor.tc_reply(q) : String}) -> {(s, (TuiColor.req_fits(q), a)) == (TuiColor.spell_req(q, ""), (True{}, TuiColor.tc_reply(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, TuiColor.spell_req(q, ""), e) : {(_, (TuiColor.req_fits(q), a)) == (TuiColor.spell_req(q, ""), (True{}, TuiColor.tc_reply(q))) : String & (Bool & String)}
  %Equal.sym(Bool, TuiColor.req_fits(q), True{}, f) : {(TuiColor.spell_req(q, ""), (_, a)) == (TuiColor.spell_req(q, ""), (True{}, TuiColor.tc_reply(q))) : String & (Bool & String)}
  %Equal.sym(String, a, TuiColor.tc_reply(q), ea) : {(TuiColor.spell_req(q, ""), (True{}, _)) == (TuiColor.spell_req(q, ""), (True{}, TuiColor.tc_reply(q))) : String & (Bool & String)}
  {==}

# a request read with input left over answers the malformed error, which
# the premise excludes
def tot.fin(+s: String, +q: FTC.Req, r: String, pre: {s == TuiColor.spell_req(q, r) : String}, f: {TuiColor.req_fits(q) == True{} : Bool}, ok: {String.eq(FTC.run.end(Wr.end(r), q), TuiColor.malformed_err()) == False{} : Bool}) -> tot.G(s, FTC.run.end(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, tot.top(s, q, FTC.answer(q), pre, f, tot.answer(q)))
    case SCon{c, rest}:
      LA.pu.absurd_tf(tot.G(s, FTC.run.end(False{}, q)), ok)

def tot.main(+s: String, d: Wr.Dec<FTC.Req>, inv: tx.Req(s, d), ok: {String.eq(FTC.run(d), TuiColor.malformed_err()) == False{} : Bool}) -> tot.G(s, FTC.run(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      tot.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LA.pu.absurd_tf(tot.G(s, FTC.run(Wr.Bad{})), ok)

def TuiColor.tui_color_ffi_total(s, other):
  tot.main(s, FTC.get_req(s), tx.req(s), other)
