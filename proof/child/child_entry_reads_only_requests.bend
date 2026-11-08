# eukhe: the proof of LAW child_entry_reads_only_requests
#
# PROOF: whatever a decoder of the entry reads is the spelling of what it
# read, then its rest, and fits the wire (cx.*, tag by tag with the wire's
# exactness laws: an unknown tag is Bad); the entry's stages carry the
# input spelled up to their field (ro.*: `pre`), so an answer that is no
# error comes from a request read whole, nothing left, and is the spelled
# model decision (ro.fin with LA.lo.answer).

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA

# s spelled up to a field a is s spelled up to its spelling b
def cx.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Decoders: what each read is its spelling, then its rest, and fits
# -----------------------------------------------------------------

def cx.MNat(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Child.ch_spell_mnat(m, r) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cx.W(s: String, d: Wr.Dec<Ch.W>) -> Type:
  match d:
    case Wr.Got{w, r}:
      {s == Child.ch_spell_w(w, r) : String} & {Child.wire_w_fits(w) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cx.Cfg(s: String, d: Wr.Dec<Ch.Cfg>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == Child.ch_spell_cfg(c, r) : String} & {Child.wire_cfg_fits(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cx.Obs(s: String, d: Wr.Dec<Ch.Obs>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == Child.ch_spell_obs(o, r) : String} & {Child.wire_obs_fits(o) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cx.Mode(s: String, d: Wr.Dec<Ch.Mode>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Child.ch_spell_mode(m, r) : String}
    case Wr.Bad{}:
      Unit

def cx.Report(s: String, d: Wr.Dec<Ch.Report>) -> Type:
  match d:
    case Wr.Got{k, r}:
      {s == Child.ch_spell_report(k, r) : String}
    case Wr.Bad{}:
      Unit

def cx.Fate(s: String, d: Wr.Dec<Ch.Fate>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == Child.ch_spell_fate(f, r) : String}
    case Wr.Bad{}:
      Unit

def cx.MFate(s: String, d: Wr.Dec<Maybe<&2, Ch.Fate>>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == Child.ch_spell_mfate(f, r) : String}
    case Wr.Bad{}:
      Unit

def cx.Ph(s: String, d: Wr.Dec<Ch.Ph>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == Child.ch_spell_ph(p, r) : String} & {Child.wire_ph_fits(p) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# Maybe<Nat>

def cx.mnat.some(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> cx.MNat(s, FCh.get_maybe_nat.some(d)):
  match d:
    case Wr.Got{+x, +s1}:
      +ee = ed
      (cx.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(x, s1), pre, Wire.wire_nat_exact(s0, x, s1, ee)), Wire.wire_nat_decoded_fits(s0, x, s1, ee))
    case Wr.Bad{}:
      Unit{}

def cx.mnat.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx.MNat(s, FCh.get_maybe_nat.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          cx.mnat.some(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n:
          Unit{}
        case 3n:
          Unit{}
        case 4n:
          Unit{}
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cx.mnat(+s: String) -> cx.MNat(s, FCh.get_maybe_nat(s)):
  cx.mnat.go(s, Wr.get_nat(s), {==})

# W

def cx.w.n(+s: String, +t: Maybe<&2, Nat>, +l: Nat, +s1: String, pre: {s == Child.ch_spell_mnat(t, Wr.put_nat(l, s1)) : String}, ft: {LawsBase.wire_mfits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(l) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> cx.W(s, FCh.get_w.n(t, l, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +ee = ed
      (cx.step(z => Child.ch_spell_mnat(t, Wr.put_nat(l, z)), s, s1, Wr.put_nat(n, s2), pre, Wire.wire_nat_exact(s1, n, s2, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), ft, LAWireSpell.ws_and_tt(LawsBase.wire_fits(l), LawsBase.wire_fits(n), fl, Wire.wire_nat_decoded_fits(s1, n, s2, ee))))
    case Wr.Bad{}:
      Unit{}

def cx.w.l(+s: String, +t: Maybe<&2, Nat>, +s0: String, pre: {s == Child.ch_spell_mnat(t, s0) : String}, ft: {LawsBase.wire_mfits(t) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> cx.W(s, FCh.get_w.l(t, d)):
  match d:
    case Wr.Got{+l, +s1}:
      +ee = ed
      cx.w.n(s, t, l, s1, cx.step(z => Child.ch_spell_mnat(t, z), s, s0, Wr.put_nat(l, s1), pre, Wire.wire_nat_exact(s0, l, s1, ee)), ft, Wire.wire_nat_decoded_fits(s0, l, s1, ee), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def cx.w.t(+s: String, d: Wr.Dec<Maybe<&2, Nat>>, xd: cx.MNat(s, d)) -> cx.W(s, FCh.get_w.t(d)):
  match d:
    case Wr.Got{+t, +s0}:
      (e0, ft) = xd
      cx.w.l(s, t, s0, e0, ft, Wr.get_nat(s0), {==})
    case Wr.Bad{}:
      Unit{}

def cx.w(+s: String) -> cx.W(s, FCh.get_w(s)):
  cx.w.t(s, FCh.get_maybe_nat(s), cx.mnat(s))

# Cfg

def cx.cfg.f(+s: String, +st: Nat, +s0: String, pre: {s == Wr.put_nat(st, s0) : String}, fs: {LawsBase.wire_fits(st) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> cx.Cfg(s, FCh.get_cfg.f(st, d)):
  match d:
    case Wr.Got{+fl, +s1}:
      +ee = ed
      (cx.step(z => Wr.put_nat(st, z), s, s0, Wr.put_nat(fl, s1), pre, Wire.wire_nat_exact(s0, fl, s1, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(st), LawsBase.wire_fits(fl), fs, Wire.wire_nat_decoded_fits(s0, fl, s1, ee)))
    case Wr.Bad{}:
      Unit{}

def cx.cfg.s(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx.Cfg(s, FCh.get_cfg.s(d)):
  match d:
    case Wr.Got{+st, +s0}:
      +ee = ed
      cx.cfg.f(s, st, s0, Wire.wire_nat_exact(s, st, s0, ee), Wire.wire_nat_decoded_fits(s, st, s0, ee), Wr.get_nat(s0), {==})
    case Wr.Bad{}:
      Unit{}

def cx.cfg(+s: String) -> cx.Cfg(s, FCh.get_cfg(s)):
  cx.cfg.s(s, Wr.get_nat(s), {==})

# Obs

def cx.obs.busy(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Maybe<&2, Nat>>, xd: cx.MNat(s0, d)) -> cx.Obs(s, FCh.get_obs.busy(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e1, ft) = xd
      (cx.step(z => Wr.put_nat(0n, z), s, s0, Child.ch_spell_mnat(t, s1), pre, e1), ft)
    case Wr.Bad{}:
      Unit{}

def cx.obs.answered(+s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> cx.Obs(s, FCh.get_obs.answered(d)):
  match d:
    case Wr.Got{+b, +s1}:
      (cx.step(z => Wr.put_nat(2n, z), s, s0, Wr.put_bool(b, s1), pre, Wire.wire_bool_exact(s0, b, s1, ed)), {==})
    case Wr.Bad{}:
      Unit{}

def cx.obs.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx.Obs(s, FCh.get_obs.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          cx.obs.busy(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FCh.get_maybe_nat(s0), cx.mnat(s0))
        case 1n:
          (Wire.wire_nat_exact(s, 1n, s0, ed), {==})
        case 2n:
          cx.obs.answered(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_bool(s0), {==})
        case 3n:
          (Wire.wire_nat_exact(s, 3n, s0, ed), {==})
        case 4n:
          (Wire.wire_nat_exact(s, 4n, s0, ed), {==})
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cx.obs(+s: String) -> cx.Obs(s, FCh.get_obs(s)):
  cx.obs.go(s, Wr.get_nat(s), {==})

# Mode

def cx.mode.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx.Mode(s, FCh.get_mode.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Unit{}
        case 3n:
          Unit{}
        case 4n:
          Unit{}
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cx.mode(+s: String) -> cx.Mode(s, FCh.get_mode(s)):
  cx.mode.go(s, Wr.get_nat(s), {==})

# Report

def cx.report.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx.Report(s, FCh.get_report.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s0, ed)
        case 4n:
          Wire.wire_nat_exact(s, 4n, s0, ed)
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cx.report(+s: String) -> cx.Report(s, FCh.get_report(s)):
  cx.report.go(s, Wr.get_nat(s), {==})

# Fate and Maybe<Fate>

def cx.fate.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx.Fate(s, FCh.get_fate.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n:
          Unit{}
        case 4n:
          Unit{}
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cx.fate(+s: String) -> cx.Fate(s, FCh.get_fate(s)):
  cx.fate.go(s, Wr.get_nat(s), {==})

def cx.mfate.some(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Ch.Fate>, xd: cx.Fate(s0, d)) -> cx.MFate(s, FCh.get_mfate.some(d)):
  match d:
    case Wr.Got{+x, +s1}:
      cx.step(z => Wr.put_nat(1n, z), s, s0, Child.ch_spell_fate(x, s1), pre, xd)
    case Wr.Bad{}:
      Unit{}

def cx.mfate.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx.MFate(s, FCh.get_mfate.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          cx.mfate.some(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FCh.get_fate(s0), cx.fate(s0))
        case 2n:
          Unit{}
        case 3n:
          Unit{}
        case 4n:
          Unit{}
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cx.mfate(+s: String) -> cx.MFate(s, FCh.get_mfate(s)):
  cx.mfate.go(s, Wr.get_nat(s), {==})

# Ph

def cx.ph.watching(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Ch.W>, xd: cx.W(s0, d)) -> cx.Ph(s, FCh.get_ph.watching(d)):
  match d:
    case Wr.Got{+w, +s1}:
      (e1, fw) = xd
      (cx.step(z => Wr.put_nat(0n, z), s, s0, Child.ch_spell_w(w, s1), pre, e1), fw)
    case Wr.Bad{}:
      Unit{}

def cx.ph.n(+s: String, +k: Ch.Report, +s1: String, pre: {s == Wr.put_nat(1n, Child.ch_spell_report(k, s1)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> cx.Ph(s, FCh.get_ph.n(k, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +ee = ed
      (cx.step(z => Wr.put_nat(1n, Child.ch_spell_report(k, z)), s, s1, Wr.put_nat(n, s2), pre, Wire.wire_nat_exact(s1, n, s2, ee)), Wire.wire_nat_decoded_fits(s1, n, s2, ee))
    case Wr.Bad{}:
      Unit{}

def cx.ph.owing(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Ch.Report>, xd: cx.Report(s0, d)) -> cx.Ph(s, FCh.get_ph.owing(d)):
  match d:
    case Wr.Got{+k, +s1}:
      cx.ph.n(s, k, s1, cx.step(z => Wr.put_nat(1n, z), s, s0, Child.ch_spell_report(k, s1), pre, xd), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def cx.ph.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx.Ph(s, FCh.get_ph.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          cx.ph.watching(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FCh.get_w(s0), cx.w(s0))
        case 1n:
          cx.ph.owing(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FCh.get_report(s0), cx.report(s0))
        case 2n:
          (Wire.wire_nat_exact(s, 2n, s0, ed), {==})
        case 3n:
          Unit{}
        case 4n:
          Unit{}
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def cx.ph(+s: String) -> cx.Ph(s, FCh.get_ph(s)):
  cx.ph.go(s, Wr.get_nat(s), {==})

# The entry's stages
# ------------------

def ro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FCh.Req, r => {(s, (Child.ch_req_fits(r), a)) == (Child.ch_spell_req(r, ""), (True{}, Child.ch_spell_answer(r))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def ro.top_eq(+s: String, +r: FCh.Req, +a: String, e: {s == Child.ch_spell_req(r, "") : String}, f: {Child.ch_req_fits(r) == True{} : Bool}, ea: {a == Child.ch_spell_answer(r) : String}) -> {(s, (Child.ch_req_fits(r), a)) == (Child.ch_spell_req(r, ""), (True{}, Child.ch_spell_answer(r))) : String & (Bool & String)}:
  %Equal.sym(String, s, Child.ch_spell_req(r, ""), e) : {(_, (Child.ch_req_fits(r), a)) == (Child.ch_spell_req(r, ""), (True{}, Child.ch_spell_answer(r))) : String & (Bool & String)}
  %Equal.sym(Bool, Child.ch_req_fits(r), True{}, f) : {(Child.ch_spell_req(r, ""), (_, a)) == (Child.ch_spell_req(r, ""), (True{}, Child.ch_spell_answer(r))) : String & (Bool & String)}
  %Equal.sym(String, a, Child.ch_spell_answer(r), ea) : {(Child.ch_spell_req(r, ""), (True{}, _)) == (Child.ch_spell_req(r, ""), (True{}, Child.ch_spell_answer(r))) : String & (Bool & String)}
  {==}

# the last stage: nothing left answers the request, anything left is the
# error form
def ro.fin(+s: String, +r: FCh.Req, s5: String, pre: {s == Child.ch_spell_req(r, s5) : String}, f: {Child.ch_req_fits(r) == True{} : Bool}, ok: {LawsBase.wire_opens_err(LA.lo.fin(r, Wr.end(s5))) == False{} : Bool}) -> ro.G(s, LA.lo.fin(r, Wr.end(s5))):
  match s5:
    case SNil{}:
      (r, ro.top_eq(s, r, LA.lo.fin(r, True{}), pre, f, LA.lo.answer(r)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(ro.G(s, LA.lo.fin(r, False{})), LA.lo.left_ok(r, ok))

# verdict: settings, clock, elapsed ms, poll, mode

def ro.vm(+s: String, +c: Ch.Cfg, +w: Ch.W, +e: Nat, +o: Ch.Obs, +s4: String, pre: {s == Wr.put_nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_spell_obs(o, s4))))) : String}, f: {Bool.and(Child.wire_cfg_fits(c), Bool.and(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o)))) == True{} : Bool}, d: Wr.Dec<Ch.Mode>, xd: cx.Mode(s4, d), ok: {LawsBase.wire_opens_err(FCh.verdict.m(c, w, e, o, d)) == False{} : Bool}) -> ro.G(s, FCh.verdict.m(c, w, e, o, d)):
  match d:
    case Wr.Got{+m, +s5}:
      ro.fin(s, FCh.AskVerdict{c, w, e, o, m}, s5, cx.step(z => Wr.put_nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, Child.ch_spell_obs(o, z))))), s, s4, Child.ch_spell_mode(m, s5), pre, xd), f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad mode")), ok)

def ro.vo(+s: String, +c: Ch.Cfg, +w: Ch.W, +e: Nat, +s3: String, pre: {s == Wr.put_nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, s3)))) : String}, fc: {Child.wire_cfg_fits(c) == True{} : Bool}, fw: {Child.wire_w_fits(w) == True{} : Bool}, fe: {LawsBase.wire_fits(e) == True{} : Bool}, d: Wr.Dec<Ch.Obs>, xd: cx.Obs(s3, d), ok: {LawsBase.wire_opens_err(FCh.verdict.o(c, w, e, d)) == False{} : Bool}) -> ro.G(s, FCh.verdict.o(c, w, e, d)):
  match d:
    case Wr.Got{+o, +s4}:
      (e4, fo) = xd
      +f = LAWireSpell.ws_and_tt(Child.wire_cfg_fits(c), Bool.and(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o))), fc, LAWireSpell.ws_and_tt(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o)), fw, LAWireSpell.ws_and_tt(LawsBase.wire_fits(e), Child.wire_obs_fits(o), fe, fo)))
      ro.vm(s, c, w, e, o, s4, cx.step(z => Wr.put_nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, Wr.put_nat(e, z)))), s, s3, Child.ch_spell_obs(o, s4), pre, e4), f, FCh.get_mode(s4), cx.mode(s4), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad poll")), ok)

def ro.ve(+s: String, +c: Ch.Cfg, +w: Ch.W, +s2: String, pre: {s == Wr.put_nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, s2))) : String}, fc: {Child.wire_cfg_fits(c) == True{} : Bool}, fw: {Child.wire_w_fits(w) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FCh.verdict.e(c, w, d)) == False{} : Bool}) -> ro.G(s, FCh.verdict.e(c, w, d)):
  match d:
    case Wr.Got{+e, +s3}:
      +ee = ed
      ro.vo(s, c, w, e, s3, cx.step(z => Wr.put_nat(0n, Child.ch_spell_cfg(c, Child.ch_spell_w(w, z))), s, s2, Wr.put_nat(e, s3), pre, Wire.wire_nat_exact(s2, e, s3, ee)), fc, fw, Wire.wire_nat_decoded_fits(s2, e, s3, ee), FCh.get_obs(s3), cx.obs(s3), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad elapsed ms")), ok)

def ro.vw(+s: String, +c: Ch.Cfg, +s1: String, pre: {s == Wr.put_nat(0n, Child.ch_spell_cfg(c, s1)) : String}, fc: {Child.wire_cfg_fits(c) == True{} : Bool}, d: Wr.Dec<Ch.W>, xd: cx.W(s1, d), ok: {LawsBase.wire_opens_err(FCh.verdict.w(c, d)) == False{} : Bool}) -> ro.G(s, FCh.verdict.w(c, d)):
  match d:
    case Wr.Got{+w, +s2}:
      (e2, fw) = xd
      ro.ve(s, c, w, s2, cx.step(z => Wr.put_nat(0n, Child.ch_spell_cfg(c, z)), s, s1, Child.ch_spell_w(w, s2), pre, e2), fc, fw, Wr.get_nat(s2), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad clock")), ok)

def ro.vc(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Ch.Cfg>, xd: cx.Cfg(s0, d), ok: {LawsBase.wire_opens_err(FCh.verdict.c(d)) == False{} : Bool}) -> ro.G(s, FCh.verdict.c(d)):
  match d:
    case Wr.Got{+c, +s1}:
      (e1, fc) = xd
      ro.vw(s, c, s1, cx.step(z => Wr.put_nat(0n, z), s, s0, Child.ch_spell_cfg(c, s1), pre, e1), fc, FCh.get_w(s1), cx.w(s1), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad settings")), ok)

# move: fate, id

def ro.mn(+s: String, +f: Maybe<&2, Ch.Fate>, +s1: String, pre: {s == Wr.put_nat(1n, Child.ch_spell_mfate(f, s1)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FCh.move.n(f, d)) == False{} : Bool}) -> ro.G(s, FCh.move.n(f, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +ee = ed
      ro.fin(s, FCh.AskMove{f, n}, s2, cx.step(z => Wr.put_nat(1n, Child.ch_spell_mfate(f, z)), s, s1, Wr.put_nat(n, s2), pre, Wire.wire_nat_exact(s1, n, s2, ee)), Wire.wire_nat_decoded_fits(s1, n, s2, ee), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad id")), ok)

def ro.mf(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Maybe<&2, Ch.Fate>>, xd: cx.MFate(s0, d), ok: {LawsBase.wire_opens_err(FCh.move.f(d)) == False{} : Bool}) -> ro.G(s, FCh.move.f(d)):
  match d:
    case Wr.Got{+f, +s1}:
      ro.mn(s, f, s1, cx.step(z => Wr.put_nat(1n, z), s, s0, Child.ch_spell_mfate(f, s1), pre, xd), Wr.get_nat(s1), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad fate")), ok)

# abort: phase, delete flag

def ro.ad(+s: String, +p: Ch.Ph, +s1: String, pre: {s == Wr.put_nat(2n, Child.ch_spell_ph(p, s1)) : String}, fp: {Child.wire_ph_fits(p) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}, ok: {LawsBase.wire_opens_err(FCh.abort.d(p, d)) == False{} : Bool}) -> ro.G(s, FCh.abort.d(p, d)):
  match d:
    case Wr.Got{+b, +s2}:
      ro.fin(s, FCh.AskAbort{p, b}, s2, cx.step(z => Wr.put_nat(2n, Child.ch_spell_ph(p, z)), s, s1, Wr.put_bool(b, s2), pre, Wire.wire_bool_exact(s1, b, s2, ed)), fp, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad delete flag")), ok)

def ro.ap(+s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<Ch.Ph>, xd: cx.Ph(s0, d), ok: {LawsBase.wire_opens_err(FCh.abort.ph(d)) == False{} : Bool}) -> ro.G(s, FCh.abort.ph(d)):
  match d:
    case Wr.Got{+p, +s1}:
      (e1, fp) = xd
      ro.ad(s, p, s1, cx.step(z => Wr.put_nat(2n, z), s, s0, Child.ch_spell_ph(p, s1), pre, e1), fp, Wr.get_bool(s1), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad phase")), ok)

# the request tag

def ro.run(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FCh.run(d)) == False{} : Bool}) -> ro.G(s, FCh.run(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          ro.vc(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FCh.get_cfg(s0), cx.cfg(s0), ok)
        case 1n:
          ro.mf(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FCh.get_mfate(s0), cx.mfate(s0), ok)
        case 2n:
          ro.ap(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), FCh.get_ph(s0), cx.ph(s0), ok)
        case 3n:
          LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: unknown request")), ok)
        case 4n:
          LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: unknown request")), ok)
        case 5n+k:
          LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: unknown request")), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("child: bad request")), ok)

def Child.child_entry_reads_only_requests(s, ok):
  ro.run(s, Wr.get_nat(s), {==}, ok)
