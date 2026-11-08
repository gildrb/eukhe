# eukhe: the proof of LAW metric_line_sound
# Each parser stage inverted: what a stage read is the text the spec
# spells for it, and of the grammar's class. The witness is the parts the
# parser built.

import Base
import ../../bend/autoresearch/line.bend as L
import ../../spec/autoresearch/decimal.bend as SD
import ../../spec/autoresearch/metric_line.bend as SL
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/line.bend as AL

# the parts spell s and are well formed
def als.G(p: L.Parts, s: String) -> Type:
  {SL.line(p) == s : String} & {SL.ok(p) == True{} : Bool}

# the line, read up to: the blanks; the name; '='; the integer digits
def als.V(sp: String, r: String) -> String:
  String.append("METRIC", String.append(sp, r))

def als.W(sp: String, name: String, r: String) -> String:
  String.append("METRIC", String.append(sp, String.append(name, r)))

def als.Z(sp: String, name: String, w: String) -> String:
  String.append("METRIC", String.append(sp, String.append(name, SCon{'=', w})))

def als.Y(sp: String, name: String, neg: Bool, u: String) -> String:
  String.append("METRIC", String.append(sp, String.append(name, SCon{'=', SL.spell_sign(neg, u)})))

def als.X(sp: String, name: String, neg: Bool, int: List<&2, Nat>, r: String) -> String:
  String.append("METRIC", String.append(sp, String.append(name, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, r))})))

# The end: the parts the parser built
# -----------------------------------

def als.fin(+sp: String, +name: String, -neg: Bool, +int: List<&2, Nat>, +frac: Maybe<&2, List<&2, Nat>>, +trail: String, -p: L.Parts, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, hf: {SL.frac_ok(frac) == True{} : Bool}, ht: {SL.all_trail(trail) == True{} : Bool}, pe: {L.Parts{sp, name, neg, int, frac, trail} == p : L.Parts}) -> als.G(p, SL.line(L.Parts{sp, name, neg, int, frac, trail})):
  %pe : als.G(_, SL.line(L.Parts{sp, name, neg, int, frac, trail}))
  ({==}, AL.al.and_tt(Bool.and(SL.nonempty(sp), SL.all_blank(sp)), Bool.and(Bool.and(SL.nonempty(name), SL.all_name(name)), Bool.and(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)))), hs, AL.al.and_tt(Bool.and(SL.nonempty(name), SL.all_name(name)), Bool.and(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail))), hn, AL.al.and_tt(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)), hi, AL.al.and_tt(SL.frac_ok(frac), SL.all_trail(trail), hf, ht)))))

# the trailing blanks end the line
def als.take(+sp: String, +name: String, -neg: Bool, +int: List<&2, Nat>, +frac: Maybe<&2, List<&2, Nat>>, +r: String, -p: L.Parts, tb: Bool, etb: {L.trail_all(r) == tb : Bool}, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, hf: {SL.frac_ok(frac) == True{} : Bool}, e: {L.take_if(tb, L.Parts{sp, name, neg, int, frac, r}) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, SL.line(L.Parts{sp, name, neg, int, frac, r})):
  match tb:
    case True{}:
      als.fin(sp, name, neg, int, frac, r, p, hs, hn, hi, hf, Equal.trans(Bool, SL.all_trail(r), L.trail_all(r), True{}, Equal.sym(Bool, L.trail_all(r), SL.all_trail(r), AL.al.trail_eq(r)), etb), AL.al.some_inj(L.Parts, L.Parts{sp, name, neg, int, frac, r}, p, e))
    case False{}:
      AL.al.none_some(L.Parts, p, als.G(p, SL.line(L.Parts{sp, name, neg, int, frac, r})), e)

# The fraction
# ------------

def als.fds(+sp: String, +name: String, -neg: Bool, +int: List<&2, Nat>, fs: List<&2, Nat>, +r4: String, -t3: String, -p: L.Parts, e1: {SL.spell_ds(fs, r4) == t3 : String}, e2: {SD.digits_ok(fs) == True{} : Bool}, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, e: {L.pl.frac.got(sp, name, neg, int, (fs, r4)) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.X(sp, name, neg, int, SCon{'.', t3})):
  match fs:
    case Nil{}:
      AL.al.none_some(L.Parts, p, als.G(p, als.X(sp, name, neg, int, SCon{'.', t3})), e)
    case +f <> +fr:
      %e1 : als.G(p, als.X(sp, name, neg, int, SCon{'.', _}))
      als.take(sp, name, neg, int, Some{f <> fr}, r4, p, L.trail_all(r4), {==}, hs, hn, hi, e2, e)

def als.fq(+sp: String, +name: String, -neg: Bool, +int: List<&2, Nat>, -t3: String, -p: L.Parts, q: List<&2, Nat> & String, sd: AL.al.SDg(t3, q), hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, e: {L.pl.frac.got(sp, name, neg, int, q) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.X(sp, name, neg, int, SCon{'.', t3})):
  match q:
    case (fs, r4):
      match sd:
        case (e1, e2):
          als.fds(sp, name, neg, int, fs, r4, t3, p, e1, e2, hs, hn, hi, e)

def als.point(+sp: String, +name: String, -neg: Bool, +int: List<&2, Nat>, +c3: Char, +t3: String, -p: L.Parts, b: Bool, eb: {L.same_char(c3, '.') == b : Bool}, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, e: {L.pl.point(b, sp, name, neg, int, c3, t3) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.X(sp, name, neg, int, SCon{c3, t3})):
  match b:
    case True{}:
      %Equal.sym(Char, c3, '.', AL.al.char_eq(c3, '.', eb)) : als.G(p, als.X(sp, name, neg, int, SCon{_, t3}))
      als.fq(sp, name, neg, int, t3, p, L.span_d(t3), AL.al.span_d_inv(t3), hs, hn, hi, e)
    case False{}:
      als.take(sp, name, neg, int, None{}, SCon{c3, t3}, p, L.trail_all(SCon{c3, t3}), {==}, hs, hn, hi, {==}, e)

def als.frac(+sp: String, +name: String, -neg: Bool, +int: List<&2, Nat>, r3: String, -p: L.Parts, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, e: {L.pl.frac(sp, name, neg, int, r3) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.X(sp, name, neg, int, r3)):
  match r3:
    case SNil{}:
      als.fin(sp, name, neg, int, None{}, SNil{}, p, hs, hn, hi, {==}, {==}, AL.al.some_inj(L.Parts, L.Parts{sp, name, neg, int, None{}, SNil{}}, p, e))
    case SCon{+c3, t3}:
      als.point(sp, name, neg, int, c3, t3, p, L.same_char(c3, '.'), {==}, hs, hn, hi, e)

# The integer digits
# ------------------

def als.ids(+sp: String, +name: String, -neg: Bool, ds: List<&2, Nat>, r3: String, -u: String, -p: L.Parts, e1: {SL.spell_ds(ds, r3) == u : String}, e2: {SD.digits_ok(ds) == True{} : Bool}, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, e: {L.pl.int(sp, name, neg, (ds, r3)) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.Y(sp, name, neg, u)):
  match ds:
    case Nil{}:
      AL.al.none_some(L.Parts, p, als.G(p, als.Y(sp, name, neg, u)), e)
    case +d <> +t:
      %e1 : als.G(p, als.Y(sp, name, neg, _))
      als.frac(sp, name, neg, d <> t, r3, p, hs, hn, e2, e)

def als.iq(+sp: String, +name: String, -neg: Bool, -u: String, -p: L.Parts, q: List<&2, Nat> & String, sd: AL.al.SDg(u, q), hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, e: {L.pl.int(sp, name, neg, q) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.Y(sp, name, neg, u)):
  match q:
    case (ds, r3):
      match sd:
        case (e1, e2):
          als.ids(sp, name, neg, ds, r3, u, p, e1, e2, hs, hn, e)

def als.int(+sp: String, +name: String, -neg: Bool, +u: String, -p: L.Parts, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, e: {L.pl.int(sp, name, neg, L.span_d(u)) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.Y(sp, name, neg, u)):
  als.iq(sp, name, neg, u, p, L.span_d(u), AL.al.span_d_inv(u), hs, hn, e)

# The sign
# --------

def als.sat(+sp: String, +name: String, +c2: Char, +t2: String, -p: L.Parts, b: Bool, eb: {L.same_char(c2, '-') == b : Bool}, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, e: {L.pl.sign.at(b, sp, name, c2, t2) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.Z(sp, name, SCon{c2, t2})):
  match b:
    case True{}:
      %Equal.sym(Char, c2, '-', AL.al.char_eq(c2, '-', eb)) : als.G(p, als.Z(sp, name, SCon{_, t2}))
      als.int(sp, name, True{}, t2, p, hs, hn, e)
    case False{}:
      als.int(sp, name, False{}, SCon{c2, t2}, p, hs, hn, e)

def als.sign(+sp: String, +name: String, w: String, -p: L.Parts, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, e: {L.pl.sign(sp, name, w) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.Z(sp, name, w)):
  match w:
    case SNil{}:
      AL.al.none_some(L.Parts, p, als.G(p, als.Z(sp, name, SNil{})), e)
    case SCon{+c2, +t2}:
      als.sat(sp, name, c2, t2, p, L.same_char(c2, '-'), {==}, hs, hn, e)

# '='
# ---

def als.eat(+sp: String, +name: String, +c: Char, t: String, -p: L.Parts, b: Bool, eb: {L.same_char(c, '=') == b : Bool}, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, e: {L.pl.eq.at(b, sp, name, t) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.W(sp, name, SCon{c, t})):
  match b:
    case True{}:
      %Equal.sym(Char, c, '=', AL.al.char_eq(c, '=', eb)) : als.G(p, als.W(sp, name, SCon{_, t}))
      als.sign(sp, name, t, p, hs, hn, e)
    case False{}:
      AL.al.none_some(L.Parts, p, als.G(p, als.W(sp, name, SCon{c, t})), e)

def als.eq(+sp: String, +name: String, r: String, -p: L.Parts, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, e: {L.pl.eq(sp, name, r) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.W(sp, name, r)):
  match r:
    case SNil{}:
      AL.al.none_some(L.Parts, p, als.G(p, als.W(sp, name, SNil{})), e)
    case SCon{+c, t}:
      als.eat(sp, name, c, t, p, L.same_char(c, '='), {==}, hs, hn, e)

# The name
# --------

def als.nb(+sp: String, nm: String, rest2: String, -rest: String, -p: L.Parts, e1: {String.append(nm, rest2) == rest : String}, e2: {SL.all_name(nm) == True{} : Bool}, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, e: {L.pl.name(sp, (nm, rest2)) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.V(sp, rest)):
  match nm:
    case SNil{}:
      AL.al.none_some(L.Parts, p, als.G(p, als.V(sp, rest)), e)
    case SCon{+c, +t}:
      %e1 : als.G(p, als.V(sp, _))
      als.eq(sp, SCon{c, t}, rest2, p, hs, e2, e)

def als.nq(+sp: String, -rest: String, -p: L.Parts, q: String & String, sn: AL.al.SN(rest, q), hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, e: {L.pl.name(sp, q) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.V(sp, rest)):
  match q:
    case (nm, rest2):
      match sn:
        case (e1, e2):
          als.nb(sp, nm, rest2, rest, p, e1, e2, hs, e)

def als.name(+sp: String, +rest: String, -p: L.Parts, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, e: {L.pl.name(sp, L.span_n(rest)) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, als.V(sp, rest)):
  als.nq(sp, rest, p, L.span_n(rest), AL.al.span_n_inv(rest), hs, e)

# The blanks
# ----------

def als.sb(b: String, rest: String, -r: String, -p: L.Parts, e1: {String.append(b, rest) == r : String}, e2: {SL.all_blank(b) == True{} : Bool}, e: {L.pl.sp((b, rest)) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, String.append("METRIC", r)):
  match b:
    case SNil{}:
      AL.al.none_some(L.Parts, p, als.G(p, String.append("METRIC", r)), e)
    case SCon{+c, +t}:
      %e1 : als.G(p, String.append("METRIC", _))
      als.name(SCon{c, t}, rest, p, e2, e)

def als.sq(-r: String, -p: L.Parts, q: String & String, sb: AL.al.SB(r, q), e: {L.pl.sp(q) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, String.append("METRIC", r)):
  match q:
    case (b, rest):
      match sb:
        case (e1, e2):
          als.sb(b, rest, r, p, e1, e2, e)

# METRIC
# ------

def als.head(+s: String, -p: L.Parts, m: Maybe<&2, String>, em: {L.prefix("METRIC", s) == m : Maybe<&2, String>}, e: {L.pl.head(m) == Some{p} : Maybe<&2, L.Parts>}) -> als.G(p, s):
  match m:
    case None{}:
      AL.al.none_some(L.Parts, p, als.G(p, s), e)
    case Some{+r}:
      %AL.al.prefix_inv("METRIC", s, r, em) : als.G(p, _)
      als.sq(r, p, L.span_b(r), AL.al.span_b_inv(r), e)

def als.got(+s: String, -kv: L.Kv, m: Maybe<&2, L.Parts>, em: {L.parse(s) == m : Maybe<&2, L.Parts>}, got: {L.metric.of(m) == Some{kv} : Maybe<&2, L.Kv>}) -> &p: L.Parts -> {SL.line(p) == s : String} & {SL.ok(p) == True{} : Bool}:
  match m:
    case None{}:
      AL.al.none_some(L.Kv, kv, &p: L.Parts -> {SL.line(p) == s : String} & {SL.ok(p) == True{} : Bool}, got)
    case Some{+p}:
      (p, als.head(s, p, L.prefix("METRIC", s), {==}, em))

def als.sound(+s: String, -kv: L.Kv, got: {L.metric(s) == Some{kv} : Maybe<&2, L.Kv>}) -> &p: L.Parts -> {SL.line(p) == s : String} & {SL.ok(p) == True{} : Bool}:
  als.got(s, kv, L.parse(s), {==}, got)

def Autoresearch.metric_line_sound(s, kv, got):
  als.sound(s, kv, got)
