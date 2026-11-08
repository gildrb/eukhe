# eukhe: the proof of LAW autoresearch_entry_exact
#
# Every input the entry reads whole as a request q is exactly the laws'
# spelling of q, and q fits the wire: each decoder stage, given what its
# sub-decoder read, turns the input into the spelling of that part (the
# wire's exactness laws), and the decoded Nats and strings fit (the wire's
# decoded-fits laws). Any other input keeps the state and answers the
# malformed error.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_autoresearch.bend as FAr
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/autoresearch/entry.bend as AutoresearchEntry
import ../wire/wire_nat_exact.bend as PWNatExact
import ../wire/wire_str_exact.bend as PWStrExact
import ../wire/wire_bool_exact.bend as PWBoolExact
import ../wire/wire_strs_exact.bend as PWStrsExact
import ../wire/wire_nat_decoded_fits.bend as PWNatFits
import ../wire/wire_str_decoded_fits.bend as PWStrFits
import ../wire/wire_strs_decoded_fit.bend as PWStrsFits
import ./base/entry.bend as LAE

# Claims per decoder
# ------------------

def ae.Cdir(d: Wr.Dec<ArS.Dir>, s: String) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_nat(AutoresearchEntry.ar_w_dir(x), r) : String}
    case Wr.Bad{}:
      Unit

def ae.Cmode(d: Wr.Dec<ArS.Mode>, s: String) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_nat(AutoresearchEntry.ar_w_mode(x), r) : String}
    case Wr.Bad{}:
      Unit

def ae.Cstatus(d: Wr.Dec<ArS.Status>, s: String) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_nat(AutoresearchEntry.ar_w_status(x), r) : String}
    case Wr.Bad{}:
      Unit

def ae.Cmnat(d: Wr.Dec<Maybe<&2, Nat>>, s: String) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == AutoresearchEntry.ar_w_mnat(x, r) : String} & {AutoresearchEntry.ar_fits_mnat(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ae.Cmstr(d: Wr.Dec<Maybe<&2, String>>, s: String) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == AutoresearchEntry.ar_w_mstr(x, r) : String} & {AutoresearchEntry.ar_fits_mstr(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ae.Ccfg(d: Wr.Dec<ArS.Cfg>, s: String) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == AutoresearchEntry.ar_w_cfg(x, r) : String} & {AutoresearchEntry.ar_fits_cfg(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a request read whole
def ae.CQ(d: Wr.Dec<FAr.Q>, i: String) -> Type:
  match d:
    case Wr.Got{q, r}:
      match r:
        case SNil{}:
          {AutoresearchEntry.ar_w_req(q) == i : String} & {AutoresearchEntry.ar_fits(q) == True{} : Bool}
        case SCon{c, t}:
          Unit
    case Wr.Bad{}:
      Unit

# Tags
# ----

def ae.mdir(+s: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ae.Cdir(FAr.get_dir(r), s):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, hr)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s1, hr)
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.x_dir(+s: String, +d: ArS.Dir, +rest: String, h: {FAr.get_dir(Wr.get_nat(s)) == Wr.Got{d, rest} : Wr.Dec<ArS.Dir>}) -> {s == Wr.put_nat(AutoresearchEntry.ar_w_dir(d), rest) : String}:
  %h : ae.Cdir(_, s)
  ae.mdir(s, Wr.get_nat(s), {==})

def ae.mmode(+s: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ae.Cmode(FAr.get_mode(r), s):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, hr)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s1, hr)
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.x_mode(+s: String, +m: ArS.Mode, +rest: String, h: {FAr.get_mode(Wr.get_nat(s)) == Wr.Got{m, rest} : Wr.Dec<ArS.Mode>}) -> {s == Wr.put_nat(AutoresearchEntry.ar_w_mode(m), rest) : String}:
  %h : ae.Cmode(_, s)
  ae.mmode(s, Wr.get_nat(s), {==})

def ae.mstatus(+s: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ae.Cstatus(FAr.get_status(r), s):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s1, hr)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s1, hr)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s1, hr)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s1, hr)
        case 4n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.x_status(+s: String, +t: ArS.Status, +rest: String, h: {FAr.get_status(Wr.get_nat(s)) == Wr.Got{t, rest} : Wr.Dec<ArS.Status>}) -> {s == Wr.put_nat(AutoresearchEntry.ar_w_status(t), rest) : String}:
  %h : ae.Cstatus(_, s)
  ae.mstatus(s, Wr.get_nat(s), {==})

# Maybes
# ------

def ae.mmnat1(+s: String, +s1: String, hs: {s == Wr.put_nat(1n, s1) : String}, r: Wr.Dec<Nat>, +hr: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}) -> ae.Cmnat(FAr.get_maybe.some(Nat, r), s):
  match r:
    case Wr.Got{+x, +s2}:
      %Wire.wire_nat_exact(s1, x, s2, hr) : {s == Wr.put_nat(1n, _) : String} & {LawsBase.wire_fits(x) == True{} : Bool}
      (hs, Wire.wire_nat_decoded_fits(s1, x, s2, hr))
    case Wr.Bad{}:
      Unit{}

def ae.mmnat(+s: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ae.Cmnat(FAr.get_mnat(r), s):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, hr), {==})
        case 1n:
          ae.mmnat1(s, s1, Wire.wire_nat_exact(s, 1n, s1, hr), Wr.get_nat(s1), {==})
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.x_mnat(+s: String, +m: Maybe<&2, Nat>, +rest: String, h: {FAr.get_mnat(Wr.get_nat(s)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Nat>>}) -> {s == AutoresearchEntry.ar_w_mnat(m, rest) : String} & {AutoresearchEntry.ar_fits_mnat(m) == True{} : Bool}:
  %h : ae.Cmnat(_, s)
  ae.mmnat(s, Wr.get_nat(s), {==})

def ae.mmstr1(+s: String, +s1: String, hs: {s == Wr.put_nat(1n, s1) : String}, r: Wr.Dec<String>, +hr: {Wr.get_str(s1) == r : Wr.Dec<String>}) -> ae.Cmstr(FAr.get_maybe.some(String, r), s):
  match r:
    case Wr.Got{+x, +s2}:
      %Wire.wire_str_exact(s1, x, s2, hr) : {s == Wr.put_nat(1n, _) : String} & {LawsBase.wire_fits(String.length(x)) == True{} : Bool}
      (hs, Wire.wire_str_decoded_fits(s1, x, s2, hr))
    case Wr.Bad{}:
      Unit{}

def ae.mmstr(+s: String, r: Wr.Dec<Nat>, hr: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ae.Cmstr(FAr.get_mstr(r), s):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s1, hr), {==})
        case 1n:
          ae.mmstr1(s, s1, Wire.wire_nat_exact(s, 1n, s1, hr), Wr.get_str(s1), {==})
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.x_mstr(+s: String, +m: Maybe<&2, String>, +rest: String, h: {FAr.get_mstr(Wr.get_nat(s)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}) -> {s == AutoresearchEntry.ar_w_mstr(m, rest) : String} & {AutoresearchEntry.ar_fits_mstr(m) == True{} : Bool}:
  %h : ae.Cmstr(_, s)
  ae.mmstr(s, Wr.get_nat(s), {==})

# The configuration
# -----------------

def ae.p4(+a: String, +b: String, +m: String, +u: String, x: String) -> String:
  Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, Wr.put_str(u, x))))

def ae.p5(+a: String, +b: String, +m: String, +u: String, +d: ArS.Dir, x: String) -> String:
  ae.p4(a, b, m, u, Wr.put_nat(AutoresearchEntry.ar_w_dir(d), x))

def ae.cfg_fits(+a: String, +b: String, +m: String, +u: String, +f: List<&2, String>, +g: List<&2, String>, +h: List<&2, String>, +mx: Maybe<&2, Nat>,
  fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool}, fm: {AutoresearchEntry.ar_fits_str(m) == True{} : Bool}, fu: {AutoresearchEntry.ar_fits_str(u) == True{} : Bool},
  ff: {LawsBase.wire_strs_fit(f) == True{} : Bool}, fg: {LawsBase.wire_strs_fit(g) == True{} : Bool}, fh: {LawsBase.wire_strs_fit(h) == True{} : Bool}, fmx: {AutoresearchEntry.ar_fits_mnat(mx) == True{} : Bool})
  -> {Bool.and(Bool.and(AutoresearchEntry.ar_fits_str(a), Bool.and(AutoresearchEntry.ar_fits_str(b), Bool.and(AutoresearchEntry.ar_fits_str(m), AutoresearchEntry.ar_fits_str(u)))), Bool.and(Bool.and(LawsBase.wire_strs_fit(f), Bool.and(LawsBase.wire_strs_fit(g), LawsBase.wire_strs_fit(h))), AutoresearchEntry.ar_fits_mnat(mx))) == True{} : Bool}:
  LAE.ae.and(Bool.and(AutoresearchEntry.ar_fits_str(a), Bool.and(AutoresearchEntry.ar_fits_str(b), Bool.and(AutoresearchEntry.ar_fits_str(m), AutoresearchEntry.ar_fits_str(u)))), Bool.and(Bool.and(LawsBase.wire_strs_fit(f), Bool.and(LawsBase.wire_strs_fit(g), LawsBase.wire_strs_fit(h))), AutoresearchEntry.ar_fits_mnat(mx)),
    LAE.ae.and(AutoresearchEntry.ar_fits_str(a), Bool.and(AutoresearchEntry.ar_fits_str(b), Bool.and(AutoresearchEntry.ar_fits_str(m), AutoresearchEntry.ar_fits_str(u))), fa,
      LAE.ae.and(AutoresearchEntry.ar_fits_str(b), Bool.and(AutoresearchEntry.ar_fits_str(m), AutoresearchEntry.ar_fits_str(u)), fb,
        LAE.ae.and(AutoresearchEntry.ar_fits_str(m), AutoresearchEntry.ar_fits_str(u), fm, fu))),
    LAE.ae.and(Bool.and(LawsBase.wire_strs_fit(f), Bool.and(LawsBase.wire_strs_fit(g), LawsBase.wire_strs_fit(h))), AutoresearchEntry.ar_fits_mnat(mx),
      LAE.ae.and(LawsBase.wire_strs_fit(f), Bool.and(LawsBase.wire_strs_fit(g), LawsBase.wire_strs_fit(h)), ff,
        LAE.ae.and(LawsBase.wire_strs_fit(g), LawsBase.wire_strs_fit(h), fg, fh)),
      fmx))


def ae.c9.fin(+a: String, +b: String, +m: String, +u: String, +d: ArS.Dir, +f: List<&2, String>, +g: List<&2, String>, +h: List<&2, String>, +mx: Maybe<&2, Nat>, +R: String, +s8: String,
  fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool}, fm: {AutoresearchEntry.ar_fits_str(m) == True{} : Bool}, fu: {AutoresearchEntry.ar_fits_str(u) == True{} : Bool},
  ff: {LawsBase.wire_strs_fit(f) == True{} : Bool}, fg: {LawsBase.wire_strs_fit(g) == True{} : Bool}, fh: {LawsBase.wire_strs_fit(h) == True{} : Bool},
  x: {s8 == AutoresearchEntry.ar_w_mnat(mx, R) : String} & {AutoresearchEntry.ar_fits_mnat(mx) == True{} : Bool})
  -> ae.Ccfg(Wr.Got{ArS.Cfg{a, b, m, u, d, f, g, h, mx}, R}, ae.p5(a, b, m, u, d, LawsBase.wire_spell_strs(f, LawsBase.wire_spell_strs(g, LawsBase.wire_spell_strs(h, s8))))):
  (xe, xf) = x
  %Equal.sym(String, s8, AutoresearchEntry.ar_w_mnat(mx, R), xe) : {ae.p5(a, b, m, u, d, LawsBase.wire_spell_strs(f, LawsBase.wire_spell_strs(g, LawsBase.wire_spell_strs(h, _)))) == AutoresearchEntry.ar_w_cfg(ArS.Cfg{a, b, m, u, d, f, g, h, mx}, R) : String} & {AutoresearchEntry.ar_fits_cfg(ArS.Cfg{a, b, m, u, d, f, g, h, mx}) == True{} : Bool}
  ({==}, ae.cfg_fits(a, b, m, u, f, g, h, mx, fa, fb, fm, fu, ff, fg, fh, xf))

def ae.c9(+a: String, +b: String, +m: String, +u: String, +d: ArS.Dir, +f: List<&2, String>, +g: List<&2, String>, +h: List<&2, String>,
  fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool}, fm: {AutoresearchEntry.ar_fits_str(m) == True{} : Bool}, fu: {AutoresearchEntry.ar_fits_str(u) == True{} : Bool},
  ff: {LawsBase.wire_strs_fit(f) == True{} : Bool}, fg: {LawsBase.wire_strs_fit(g) == True{} : Bool}, fh: {LawsBase.wire_strs_fit(h) == True{} : Bool},
  +s8: String, r: Wr.Dec<Maybe<&2, Nat>>, hr: {FAr.get_mnat(Wr.get_nat(s8)) == r : Wr.Dec<Maybe<&2, Nat>>})
  -> ae.Ccfg(FAr.get_cfg.max(a, b, m, u, d, f, g, h, r), ae.p5(a, b, m, u, d, LawsBase.wire_spell_strs(f, LawsBase.wire_spell_strs(g, LawsBase.wire_spell_strs(h, s8))))):
  match r:
    case Wr.Got{+mx, +rr}:
      ae.c9.fin(a, b, m, u, d, f, g, h, mx, rr, s8, fa, fb, fm, fu, ff, fg, fh, ae.x_mnat(s8, mx, rr, hr))
    case Wr.Bad{}:
      Unit{}

def ae.c8(+a: String, +b: String, +m: String, +u: String, +d: ArS.Dir, +f: List<&2, String>, +g: List<&2, String>,
  fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool}, fm: {AutoresearchEntry.ar_fits_str(m) == True{} : Bool}, fu: {AutoresearchEntry.ar_fits_str(u) == True{} : Bool},
  ff: {LawsBase.wire_strs_fit(f) == True{} : Bool}, fg: {LawsBase.wire_strs_fit(g) == True{} : Bool},
  +s7: String, r: Wr.Dec<List<&2, String>>, +hr: {FAr.get_strs(s7) == r : Wr.Dec<List<&2, String>>})
  -> ae.Ccfg(FAr.get_cfg.off(a, b, m, u, d, f, g, r), ae.p5(a, b, m, u, d, LawsBase.wire_spell_strs(f, LawsBase.wire_spell_strs(g, s7)))):
  match r:
    case Wr.Got{+h, +s8}:
      %Equal.sym(String, s7, LawsBase.wire_spell_strs(h, s8), Wire.wire_strs_exact(s7, h, s8, hr)) : ae.Ccfg(FAr.get_cfg.max(a, b, m, u, d, f, g, h, FAr.get_mnat(Wr.get_nat(s8))), ae.p5(a, b, m, u, d, LawsBase.wire_spell_strs(f, LawsBase.wire_spell_strs(g, _))))
      ae.c9(a, b, m, u, d, f, g, h, fa, fb, fm, fu, ff, fg, Wire.wire_strs_decoded_fit(s7, h, s8, hr), s8, FAr.get_mnat(Wr.get_nat(s8)), {==})
    case Wr.Bad{}:
      Unit{}

def ae.c7(+a: String, +b: String, +m: String, +u: String, +d: ArS.Dir, +f: List<&2, String>,
  fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool}, fm: {AutoresearchEntry.ar_fits_str(m) == True{} : Bool}, fu: {AutoresearchEntry.ar_fits_str(u) == True{} : Bool},
  ff: {LawsBase.wire_strs_fit(f) == True{} : Bool},
  +s6: String, r: Wr.Dec<List<&2, String>>, +hr: {FAr.get_strs(s6) == r : Wr.Dec<List<&2, String>>})
  -> ae.Ccfg(FAr.get_cfg.scope(a, b, m, u, d, f, r), ae.p5(a, b, m, u, d, LawsBase.wire_spell_strs(f, s6))):
  match r:
    case Wr.Got{+g, +s7}:
      %Equal.sym(String, s6, LawsBase.wire_spell_strs(g, s7), Wire.wire_strs_exact(s6, g, s7, hr)) : ae.Ccfg(FAr.get_cfg.off(a, b, m, u, d, f, g, FAr.get_strs(s7)), ae.p5(a, b, m, u, d, LawsBase.wire_spell_strs(f, _)))
      ae.c8(a, b, m, u, d, f, g, fa, fb, fm, fu, ff, Wire.wire_strs_decoded_fit(s6, g, s7, hr), s7, FAr.get_strs(s7), {==})
    case Wr.Bad{}:
      Unit{}

def ae.c6(+a: String, +b: String, +m: String, +u: String, +d: ArS.Dir,
  fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool}, fm: {AutoresearchEntry.ar_fits_str(m) == True{} : Bool}, fu: {AutoresearchEntry.ar_fits_str(u) == True{} : Bool},
  +s5: String, r: Wr.Dec<List<&2, String>>, +hr: {FAr.get_strs(s5) == r : Wr.Dec<List<&2, String>>})
  -> ae.Ccfg(FAr.get_cfg.sec(a, b, m, u, d, r), ae.p5(a, b, m, u, d, s5)):
  match r:
    case Wr.Got{+f, +s6}:
      %Equal.sym(String, s5, LawsBase.wire_spell_strs(f, s6), Wire.wire_strs_exact(s5, f, s6, hr)) : ae.Ccfg(FAr.get_cfg.scope(a, b, m, u, d, f, FAr.get_strs(s6)), ae.p5(a, b, m, u, d, _))
      ae.c7(a, b, m, u, d, f, fa, fb, fm, fu, Wire.wire_strs_decoded_fit(s5, f, s6, hr), s6, FAr.get_strs(s6), {==})
    case Wr.Bad{}:
      Unit{}

def ae.c5(+a: String, +b: String, +m: String, +u: String,
  fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool}, fm: {AutoresearchEntry.ar_fits_str(m) == True{} : Bool}, fu: {AutoresearchEntry.ar_fits_str(u) == True{} : Bool},
  +s4: String, r: Wr.Dec<ArS.Dir>, hr: {FAr.get_dir(Wr.get_nat(s4)) == r : Wr.Dec<ArS.Dir>})
  -> ae.Ccfg(FAr.get_cfg.dir(a, b, m, u, r), ae.p4(a, b, m, u, s4)):
  match r:
    case Wr.Got{+d, +s5}:
      %Equal.sym(String, s4, Wr.put_nat(AutoresearchEntry.ar_w_dir(d), s5), ae.x_dir(s4, d, s5, hr)) : ae.Ccfg(FAr.get_cfg.sec(a, b, m, u, d, FAr.get_strs(s5)), ae.p4(a, b, m, u, _))
      ae.c6(a, b, m, u, d, fa, fb, fm, fu, s5, FAr.get_strs(s5), {==})
    case Wr.Bad{}:
      Unit{}

def ae.c4(+a: String, +b: String, +m: String, fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool}, fm: {AutoresearchEntry.ar_fits_str(m) == True{} : Bool},
  +s3: String, r: Wr.Dec<String>, +hr: {Wr.get_str(s3) == r : Wr.Dec<String>})
  -> ae.Ccfg(FAr.get_cfg.unit(a, b, m, r), Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, s3)))):
  match r:
    case Wr.Got{+u, +s4}:
      %Equal.sym(String, s3, Wr.put_str(u, s4), Wire.wire_str_exact(s3, u, s4, hr)) : ae.Ccfg(FAr.get_cfg.dir(a, b, m, u, FAr.get_dir(Wr.get_nat(s4))), Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, _))))
      ae.c5(a, b, m, u, fa, fb, fm, Wire.wire_str_decoded_fits(s3, u, s4, hr), s4, FAr.get_dir(Wr.get_nat(s4)), {==})
    case Wr.Bad{}:
      Unit{}

def ae.c3(+a: String, +b: String, fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool}, fb: {AutoresearchEntry.ar_fits_str(b) == True{} : Bool},
  +s2: String, r: Wr.Dec<String>, +hr: {Wr.get_str(s2) == r : Wr.Dec<String>})
  -> ae.Ccfg(FAr.get_cfg.metric(a, b, r), Wr.put_str(a, Wr.put_str(b, s2))):
  match r:
    case Wr.Got{+m, +s3}:
      %Equal.sym(String, s2, Wr.put_str(m, s3), Wire.wire_str_exact(s2, m, s3, hr)) : ae.Ccfg(FAr.get_cfg.unit(a, b, m, Wr.get_str(s3)), Wr.put_str(a, Wr.put_str(b, _)))
      ae.c4(a, b, m, fa, fb, Wire.wire_str_decoded_fits(s2, m, s3, hr), s3, Wr.get_str(s3), {==})
    case Wr.Bad{}:
      Unit{}

def ae.c2(+a: String, fa: {AutoresearchEntry.ar_fits_str(a) == True{} : Bool},
  +s1: String, r: Wr.Dec<String>, +hr: {Wr.get_str(s1) == r : Wr.Dec<String>})
  -> ae.Ccfg(FAr.get_cfg.goal(a, r), Wr.put_str(a, s1)):
  match r:
    case Wr.Got{+b, +s2}:
      %Equal.sym(String, s1, Wr.put_str(b, s2), Wire.wire_str_exact(s1, b, s2, hr)) : ae.Ccfg(FAr.get_cfg.metric(a, b, Wr.get_str(s2)), Wr.put_str(a, _))
      ae.c3(a, b, fa, Wire.wire_str_decoded_fits(s1, b, s2, hr), s2, Wr.get_str(s2), {==})
    case Wr.Bad{}:
      Unit{}

def ae.c1(+s0: String, r: Wr.Dec<String>, +hr: {Wr.get_str(s0) == r : Wr.Dec<String>}) -> ae.Ccfg(FAr.get_cfg.name(r), s0):
  match r:
    case Wr.Got{+a, +s1}:
      %Equal.sym(String, s0, Wr.put_str(a, s1), Wire.wire_str_exact(s0, a, s1, hr)) : ae.Ccfg(FAr.get_cfg.goal(a, Wr.get_str(s1)), _)
      ae.c2(a, Wire.wire_str_decoded_fits(s0, a, s1, hr), s1, Wr.get_str(s1), {==})
    case Wr.Bad{}:
      Unit{}

def ae.x_cfg(+s: String, +c: ArS.Cfg, +rest: String, h: {FAr.get_cfg(s) == Wr.Got{c, rest} : Wr.Dec<ArS.Cfg>}) -> {s == AutoresearchEntry.ar_w_cfg(c, rest) : String} & {AutoresearchEntry.ar_fits_cfg(c) == True{} : Bool}:
  %h : ae.Ccfg(_, s)
  ae.c1(s, Wr.get_str(s), {==})

# The requests
# ------------

def ae.qharn(+c: ArS.Cfg, +f: Bool, fc: {AutoresearchEntry.ar_fits_cfg(c) == True{} : Bool}, +s3: String, r: Wr.Dec<Bool>, hr: {Wr.get_bool(s3) == r : Wr.Dec<Bool>})
  -> ae.CQ(FAr.get_init.harness(c, f, r), Wr.put_nat(0n, AutoresearchEntry.ar_w_cfg(c, Wr.put_bool(f, s3)))):
  match r:
    case Wr.Got{+h, s4}:
      match s4:
        case SNil{}:
          %Equal.sym(String, s3, Wr.put_bool(h, ""), Wire.wire_bool_exact(s3, h, "", hr)) : ae.CQ(Wr.Got{FAr.QEv{ArS.Init{c, f, h}}, ""}, Wr.put_nat(0n, AutoresearchEntry.ar_w_cfg(c, Wr.put_bool(f, _))))
          ({==}, fc)
        case SCon{c, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.qfresh(+c: ArS.Cfg, fc: {AutoresearchEntry.ar_fits_cfg(c) == True{} : Bool}, +s2: String, r: Wr.Dec<Bool>, hr: {Wr.get_bool(s2) == r : Wr.Dec<Bool>})
  -> ae.CQ(FAr.get_init.fresh(c, r), Wr.put_nat(0n, AutoresearchEntry.ar_w_cfg(c, s2))):
  match r:
    case Wr.Got{+f, +s3}:
      %Equal.sym(String, s2, Wr.put_bool(f, s3), Wire.wire_bool_exact(s2, f, s3, hr)) : ae.CQ(FAr.get_init.harness(c, f, Wr.get_bool(s3)), Wr.put_nat(0n, AutoresearchEntry.ar_w_cfg(c, _)))
      ae.qharn(c, f, fc, s3, Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def ae.qinit.got(+c: ArS.Cfg, +s1: String, +s2: String, x: {s1 == AutoresearchEntry.ar_w_cfg(c, s2) : String} & {AutoresearchEntry.ar_fits_cfg(c) == True{} : Bool})
  -> ae.CQ(FAr.get_init(Wr.Got{c, s2}), Wr.put_nat(0n, s1)):
  (xe, xf) = x
  %Equal.sym(String, s1, AutoresearchEntry.ar_w_cfg(c, s2), xe) : ae.CQ(FAr.get_init.fresh(c, Wr.get_bool(s2)), Wr.put_nat(0n, _))
  ae.qfresh(c, xf, s2, Wr.get_bool(s2), {==})

def ae.qinit(+s1: String, r: Wr.Dec<ArS.Cfg>, hr: {FAr.get_cfg(s1) == r : Wr.Dec<ArS.Cfg>}) -> ae.CQ(FAr.get_init(r), Wr.put_nat(0n, s1)):
  match r:
    case Wr.Got{+c, +s2}:
      ae.qinit.got(c, s1, s2, ae.x_cfg(s1, c, s2, hr))
    case Wr.Bad{}:
      Unit{}

def ae.qbegin(+s1: String, r: Wr.Dec<Nat>, +hr: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}) -> ae.CQ(FAr.get_begin(r), Wr.put_nat(1n, s1)):
  match r:
    case Wr.Got{+n, s2}:
      match s2:
        case SNil{}:
          %Equal.sym(String, s1, Wr.put_nat(n, ""), Wire.wire_nat_exact(s1, n, "", hr)) : ae.CQ(Wr.Got{FAr.QEv{ArS.Begin{n}}, ""}, Wr.put_nat(1n, _))
          ({==}, Wire.wire_nat_decoded_fits(s1, n, "", hr))
        case SCon{c, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.qline(+s1: String, r: Wr.Dec<String>, +hr: {Wr.get_str(s1) == r : Wr.Dec<String>}) -> ae.CQ(FAr.get_line(r), Wr.put_nat(2n, s1)):
  match r:
    case Wr.Got{+t, s2}:
      match s2:
        case SNil{}:
          %Equal.sym(String, s1, Wr.put_str(t, ""), Wire.wire_str_exact(s1, t, "", hr)) : ae.CQ(Wr.Got{FAr.QEv{ArS.Line{t}}, ""}, Wr.put_nat(2n, _))
          ({==}, Wire.wire_str_decoded_fits(s1, t, "", hr))
        case SCon{c, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.qto(+neg: Bool, +code: Nat, fcode: {LawsBase.wire_fits(code) == True{} : Bool}, +s3: String, r: Wr.Dec<Bool>, hr: {Wr.get_bool(s3) == r : Wr.Dec<Bool>})
  -> ae.CQ(FAr.get_finish.timeout(neg, code, r), Wr.put_nat(3n, Wr.put_bool(neg, Wr.put_nat(code, s3)))):
  match r:
    case Wr.Got{+to, s4}:
      match s4:
        case SNil{}:
          %Equal.sym(String, s3, Wr.put_bool(to, ""), Wire.wire_bool_exact(s3, to, "", hr)) : ae.CQ(Wr.Got{FAr.QEv{ArS.Finish{neg, code, to}}, ""}, Wr.put_nat(3n, Wr.put_bool(neg, Wr.put_nat(code, _))))
          ({==}, fcode)
        case SCon{c, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.qcode(+neg: Bool, +s2: String, r: Wr.Dec<Nat>, +hr: {Wr.get_nat(s2) == r : Wr.Dec<Nat>}) -> ae.CQ(FAr.get_finish.code(neg, r), Wr.put_nat(3n, Wr.put_bool(neg, s2))):
  match r:
    case Wr.Got{+code, +s3}:
      %Equal.sym(String, s2, Wr.put_nat(code, s3), Wire.wire_nat_exact(s2, code, s3, hr)) : ae.CQ(FAr.get_finish.timeout(neg, code, Wr.get_bool(s3)), Wr.put_nat(3n, Wr.put_bool(neg, _)))
      ae.qto(neg, code, Wire.wire_nat_decoded_fits(s2, code, s3, hr), s3, Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def ae.qfin(+s1: String, r: Wr.Dec<Bool>, hr: {Wr.get_bool(s1) == r : Wr.Dec<Bool>}) -> ae.CQ(FAr.get_finish(r), Wr.put_nat(3n, s1)):
  match r:
    case Wr.Got{+neg, +s2}:
      %Equal.sym(String, s1, Wr.put_bool(neg, s2), Wire.wire_bool_exact(s1, neg, s2, hr)) : ae.CQ(FAr.get_finish.code(neg, Wr.get_nat(s2)), Wr.put_nat(3n, _))
      ae.qcode(neg, s2, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def ae.qdevs(+st: ArS.Status, +desc: String, +why: Maybe<&2, String>, fdesc: {AutoresearchEntry.ar_fits_str(desc) == True{} : Bool}, fwhy: {AutoresearchEntry.ar_fits_mstr(why) == True{} : Bool},
  +s4: String, r: Wr.Dec<Nat>, +hr: {Wr.get_nat(s4) == r : Wr.Dec<Nat>})
  -> ae.CQ(FAr.get_log.devs(st, desc, why, r), Wr.put_nat(4n, Wr.put_nat(AutoresearchEntry.ar_w_status(st), Wr.put_str(desc, AutoresearchEntry.ar_w_mstr(why, s4))))):
  match r:
    case Wr.Got{+n, s5}:
      match s5:
        case SNil{}:
          %Equal.sym(String, s4, Wr.put_nat(n, ""), Wire.wire_nat_exact(s4, n, "", hr)) : ae.CQ(Wr.Got{FAr.QEv{ArS.Log{st, desc, why, n}}, ""}, Wr.put_nat(4n, Wr.put_nat(AutoresearchEntry.ar_w_status(st), Wr.put_str(desc, AutoresearchEntry.ar_w_mstr(why, _)))))
          ({==}, LAE.ae.and(AutoresearchEntry.ar_fits_str(desc), Bool.and(AutoresearchEntry.ar_fits_mstr(why), LawsBase.wire_fits(n)), fdesc, LAE.ae.and(AutoresearchEntry.ar_fits_mstr(why), LawsBase.wire_fits(n), fwhy, Wire.wire_nat_decoded_fits(s4, n, "", hr))))
        case SCon{c, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.qwhy.got(+st: ArS.Status, +desc: String, +why: Maybe<&2, String>, fdesc: {AutoresearchEntry.ar_fits_str(desc) == True{} : Bool}, +s3: String, +s4: String,
  x: {s3 == AutoresearchEntry.ar_w_mstr(why, s4) : String} & {AutoresearchEntry.ar_fits_mstr(why) == True{} : Bool})
  -> ae.CQ(FAr.get_log.why(st, desc, Wr.Got{why, s4}), Wr.put_nat(4n, Wr.put_nat(AutoresearchEntry.ar_w_status(st), Wr.put_str(desc, s3)))):
  (xe, xf) = x
  %Equal.sym(String, s3, AutoresearchEntry.ar_w_mstr(why, s4), xe) : ae.CQ(FAr.get_log.devs(st, desc, why, Wr.get_nat(s4)), Wr.put_nat(4n, Wr.put_nat(AutoresearchEntry.ar_w_status(st), Wr.put_str(desc, _))))
  ae.qdevs(st, desc, why, fdesc, xf, s4, Wr.get_nat(s4), {==})

def ae.qwhy(+st: ArS.Status, +desc: String, fdesc: {AutoresearchEntry.ar_fits_str(desc) == True{} : Bool}, +s3: String, r: Wr.Dec<Maybe<&2, String>>, hr: {FAr.get_mstr(Wr.get_nat(s3)) == r : Wr.Dec<Maybe<&2, String>>})
  -> ae.CQ(FAr.get_log.why(st, desc, r), Wr.put_nat(4n, Wr.put_nat(AutoresearchEntry.ar_w_status(st), Wr.put_str(desc, s3)))):
  match r:
    case Wr.Got{+why, +s4}:
      ae.qwhy.got(st, desc, why, fdesc, s3, s4, ae.x_mstr(s3, why, s4, hr))
    case Wr.Bad{}:
      Unit{}

def ae.qdesc(+st: ArS.Status, +s2: String, r: Wr.Dec<String>, +hr: {Wr.get_str(s2) == r : Wr.Dec<String>})
  -> ae.CQ(FAr.get_log.desc(st, r), Wr.put_nat(4n, Wr.put_nat(AutoresearchEntry.ar_w_status(st), s2))):
  match r:
    case Wr.Got{+desc, +s3}:
      %Equal.sym(String, s2, Wr.put_str(desc, s3), Wire.wire_str_exact(s2, desc, s3, hr)) : ae.CQ(FAr.get_log.why(st, desc, FAr.get_mstr(Wr.get_nat(s3))), Wr.put_nat(4n, Wr.put_nat(AutoresearchEntry.ar_w_status(st), _)))
      ae.qwhy(st, desc, Wire.wire_str_decoded_fits(s2, desc, s3, hr), s3, FAr.get_mstr(Wr.get_nat(s3)), {==})
    case Wr.Bad{}:
      Unit{}

def ae.qlog(+s1: String, r: Wr.Dec<ArS.Status>, hr: {FAr.get_status(Wr.get_nat(s1)) == r : Wr.Dec<ArS.Status>}) -> ae.CQ(FAr.get_log(r), Wr.put_nat(4n, s1)):
  match r:
    case Wr.Got{+st, +s2}:
      %Equal.sym(String, s1, Wr.put_nat(AutoresearchEntry.ar_w_status(st), s2), ae.x_status(s1, st, s2, hr)) : ae.CQ(FAr.get_log.desc(st, Wr.get_str(s2)), Wr.put_nat(4n, _))
      ae.qdesc(st, s2, Wr.get_str(s2), {==})
    case Wr.Bad{}:
      Unit{}

def ae.qreason(+n: Nat, fn: {LawsBase.wire_fits(n) == True{} : Bool}, +s2: String, r: Wr.Dec<String>, +hr: {Wr.get_str(s2) == r : Wr.Dec<String>})
  -> ae.CQ(FAr.get_flag.reason(n, r), Wr.put_nat(5n, Wr.put_nat(n, s2))):
  match r:
    case Wr.Got{+t, s3}:
      match s3:
        case SNil{}:
          %Equal.sym(String, s2, Wr.put_str(t, ""), Wire.wire_str_exact(s2, t, "", hr)) : ae.CQ(Wr.Got{FAr.QEv{ArS.Flag{n, t}}, ""}, Wr.put_nat(5n, Wr.put_nat(n, _)))
          ({==}, LAE.ae.and(LawsBase.wire_fits(n), AutoresearchEntry.ar_fits_str(t), fn, Wire.wire_str_decoded_fits(s2, t, "", hr)))
        case SCon{c, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.qflag(+s1: String, r: Wr.Dec<Nat>, +hr: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}) -> ae.CQ(FAr.get_flag(r), Wr.put_nat(5n, s1)):
  match r:
    case Wr.Got{+n, +s2}:
      %Equal.sym(String, s1, Wr.put_nat(n, s2), Wire.wire_nat_exact(s1, n, s2, hr)) : ae.CQ(FAr.get_flag.reason(n, Wr.get_str(s2)), Wr.put_nat(5n, _))
      ae.qreason(n, Wire.wire_nat_decoded_fits(s1, n, s2, hr), s2, Wr.get_str(s2), {==})
    case Wr.Bad{}:
      Unit{}

def ae.qmode(+s1: String, r: Wr.Dec<ArS.Mode>, hr: {FAr.get_mode(Wr.get_nat(s1)) == r : Wr.Dec<ArS.Mode>}) -> ae.CQ(FAr.get_set_mode(r), Wr.put_nat(6n, s1)):
  match r:
    case Wr.Got{+m, s2}:
      match s2:
        case SNil{}:
          %Equal.sym(String, s1, Wr.put_nat(AutoresearchEntry.ar_w_mode(m), ""), ae.x_mode(s1, m, "", hr)) : ae.CQ(Wr.Got{FAr.QEv{ArS.SetMode{m}}, ""}, Wr.put_nat(6n, _))
          ({==}, {==})
        case SCon{c, t}:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def ae.q0(+i: String, r: Wr.Dec<Nat>, +hr: {Wr.get_nat(i) == r : Wr.Dec<Nat>}) -> ae.CQ(FAr.get_q.go(r), i):
  match r:
    case Wr.Got{n, +s1}:
      match n:
        case 0n:
          %Equal.sym(String, i, Wr.put_nat(0n, s1), Wire.wire_nat_exact(i, 0n, s1, hr)) : ae.CQ(FAr.get_init(FAr.get_cfg(s1)), _)
          ae.qinit(s1, FAr.get_cfg(s1), {==})
        case 1n:
          %Equal.sym(String, i, Wr.put_nat(1n, s1), Wire.wire_nat_exact(i, 1n, s1, hr)) : ae.CQ(FAr.get_begin(Wr.get_nat(s1)), _)
          ae.qbegin(s1, Wr.get_nat(s1), {==})
        case 2n:
          %Equal.sym(String, i, Wr.put_nat(2n, s1), Wire.wire_nat_exact(i, 2n, s1, hr)) : ae.CQ(FAr.get_line(Wr.get_str(s1)), _)
          ae.qline(s1, Wr.get_str(s1), {==})
        case 3n:
          %Equal.sym(String, i, Wr.put_nat(3n, s1), Wire.wire_nat_exact(i, 3n, s1, hr)) : ae.CQ(FAr.get_finish(Wr.get_bool(s1)), _)
          ae.qfin(s1, Wr.get_bool(s1), {==})
        case 4n:
          %Equal.sym(String, i, Wr.put_nat(4n, s1), Wire.wire_nat_exact(i, 4n, s1, hr)) : ae.CQ(FAr.get_log(FAr.get_status(Wr.get_nat(s1))), _)
          ae.qlog(s1, FAr.get_status(Wr.get_nat(s1)), {==})
        case 5n:
          %Equal.sym(String, i, Wr.put_nat(5n, s1), Wire.wire_nat_exact(i, 5n, s1, hr)) : ae.CQ(FAr.get_flag(Wr.get_nat(s1)), _)
          ae.qflag(s1, Wr.get_nat(s1), {==})
        case 6n:
          %Equal.sym(String, i, Wr.put_nat(6n, s1), Wire.wire_nat_exact(i, 6n, s1, hr)) : ae.CQ(FAr.get_set_mode(FAr.get_mode(Wr.get_nat(s1))), _)
          ae.qmode(s1, FAr.get_mode(Wr.get_nat(s1)), {==})
        case 7n:
          match s1:
            case SNil{}:
              %Equal.sym(String, i, Wr.put_nat(7n, ""), Wire.wire_nat_exact(i, 7n, "", hr)) : ae.CQ(Wr.Got{FAr.QSnap{}, ""}, _)
              ({==}, {==})
            case SCon{c, t}:
              Unit{}
        case 8n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# The law
# -------

# an input the entry does not read whole keeps the state
def ae.keep(+s: ArS.St, +i: String, -d: Wr.Dec<FAr.Q>, hd: {FAr.get_q(i) == d : Wr.Dec<FAr.Q>}, k: {FAr.step.q(s, d) == (FAr.Live{s}, FAr.fail()) : FAr.St & String})
  -> {FAr.step(FAr.Live{s}, i) == (FAr.Live{s}, AutoresearchEntry.ar_malformed()) : FAr.St & String}:
  %Equal.sym(Wr.Dec<FAr.Q>, FAr.get_q(i), d, hd) : {FAr.step.q(s, _) == (FAr.Live{s}, AutoresearchEntry.ar_malformed()) : FAr.St & String}
  k

# an input the entry reads whole is the spelling of what it read
def ae.got(+i: String, +q: FAr.Q, hd: {FAr.get_q(i) == Wr.Got{q, ""} : Wr.Dec<FAr.Q>}) -> {AutoresearchEntry.ar_w_req(q) == i : String} & {AutoresearchEntry.ar_fits(q) == True{} : Bool}:
  %hd : ae.CQ(_, i)
  ae.q0(i, Wr.get_nat(i), {==})

def ae.ans(+s: ArS.St, +i: String, d: Wr.Dec<FAr.Q>, hd: {FAr.get_q(i) == d : Wr.Dec<FAr.Q>}) -> AutoresearchEntry.ar_answered(s, i):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          Inr{(q, ae.got(i, q, hd))}
        case SCon{c, t}:
          Inl{ae.keep(s, i, Wr.Got{q, SCon{c, t}}, hd, {==})}
    case Wr.Bad{}:
      Inl{ae.keep(s, i, Wr.Bad{}, hd, {==})}

def AutoresearchEntry.autoresearch_entry_exact(s, i):
  ae.ans(s, i, FAr.get_q(i), {==})
