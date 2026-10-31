# autoresearch/line: the METRIC lines of a benchmark's output (port of
# oh-my-pi autoresearch helpers.ts `parseMetricLines`, which uses the
# regex ^METRIC\s+([\w.µ-]+)=(\S+)\s*$ and JS Number). One line, read
# char by char (no regex):
#
#   METRIC <blanks> <name> = [-] <digits> [. <digits>] <trailing blanks>
#
# blanks: space or tab, at least one; name: at least one of A-Z a-z 0-9
# _ . -; digits: at least one 0-9 each; trailing blanks: space, tab or
# CR. The value is exact (autoresearch/dec.bend), canonical, with at most
# 15 significant digits; any other line means nothing. Pure: no IO, no
# @unsafe.

import Base
import ./dec.bend as D

# a METRIC line's parts, as written
type Parts is Data:
  Parts{sp: String, name: String, neg: Bool, int: List<&2, Nat>, frac: Maybe<&2, List<&2, Nat>>, trail: String}

# a metric's name and value
type Kv is Data:
  Kv{name: String, val: D.Dec}

def Parts.name(p: Parts) -> String:
  match p:
    case Parts{sp, name, neg, int, frac, trail}:
      name

# Chars
# -----

def code(c: Char) -> Nat:
  match c:
    case Chr{x}:
      U32.to_nat(x)

# c is the char k
def same_char(c: Char, k: Char) -> Bool:
  match c k:
    case Chr{x} Chr{y}:
      U32.is_eq(x, y)

# the blanks between METRIC and the name: space, tab
def blank(+n: Nat) -> Bool:
  Bool.or(Nat.is_eq(n, 32n), Nat.is_eq(n, 9n))

# the blanks after the value: space, tab, CR
def trail_blank(+n: Nat) -> Bool:
  Bool.or(blank(n), Nat.is_eq(n, 13n))

def within(+n: Nat, lo: Nat, hi: Nat) -> Bool:
  Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi))

# a char of a name: A-Z a-z 0-9 _ . -
def name_char(+n: Nat) -> Bool:
  Bool.or(within(n, 65n, 90n), Bool.or(within(n, 97n, 122n), Bool.or(within(n, 48n, 57n), Bool.or(Nat.is_eq(n, 95n), Bool.or(Nat.is_eq(n, 46n), Nat.is_eq(n, 45n))))))

def digit.of(ok: Bool, d: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{d}
    case False{}:
      None{}

def digit.code(+x: U32, +d: Nat) -> Maybe<&2, Nat>:
  digit.of(Bool.and(Nat.is_lt(d, 10n), U32.is_eq(x, U32.from_nat(Nat.add(48n, d)))), d)

# the digit a char is, if it is one
def digit(c: Char) -> Maybe<&2, Nat>:
  match c:
    case Chr{+x}:
      digit.code(x, Nat.sub(U32.to_nat(x), 48n))

# every char of s is a trailing blank
def trail_all(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(trail_blank(code(c)), trail_all(t))

# Spans
# -----

def span.at(b: Bool, c: Char, t: String, r: String & String) -> String & String:
  match b:
    case True{}:
      (a, rest) = r
      (SCon{c, a}, rest)
    case False{}:
      (SNil{}, SCon{c, t})

# the longest start of s of blanks, and the rest
def span_b(s: String) -> String & String:
  match s:
    case SNil{}:
      (SNil{}, SNil{})
    case SCon{+c, +t}:
      span.at(blank(code(c)), c, t, span_b(t))

# the longest start of s of name chars, and the rest
def span_n(s: String) -> String & String:
  match s:
    case SNil{}:
      (SNil{}, SNil{})
    case SCon{+c, +t}:
      span.at(name_char(code(c)), c, t, span_n(t))

def span_d.at(m: Maybe<&2, Nat>, c: Char, t: String, r: List<&2, Nat> & String) -> List<&2, Nat> & String:
  match m:
    case Some{d}:
      (a, rest) = r
      (d <> a, rest)
    case None{}:
      (Nil{}, SCon{c, t})

# the longest start of s of digits, as digits, and the rest
def span_d(s: String) -> List<&2, Nat> & String:
  match s:
    case SNil{}:
      (Nil{}, SNil{})
    case SCon{+c, +t}:
      span_d.at(digit(c), c, t, span_d(t))

def prefix.at(ok: Bool, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      r
    case False{}:
      None{}

# s less the prefix p, when s starts with it
def prefix(p: String, s: String) -> Maybe<&2, String>:
  match p:
    case SNil{}:
      Some{s}
    case SCon{pc, pt}:
      match s:
        case SNil{}:
          None{}
        case SCon{c, t}:
          prefix.at(same_char(c, pc), prefix(pt, t))

# The line
# --------

def some(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      True{}

def any_d(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      True{}

def take_if(ok: Bool, p: Parts) -> Maybe<&2, Parts>:
  match ok:
    case True{}:
      Some{p}
    case False{}:
      None{}

# the trailing blanks end the line
def pl.trail(sp: String, name: String, neg: Bool, int: List<&2, Nat>, frac: Maybe<&2, List<&2, Nat>>, +rest: String) -> Maybe<&2, Parts>:
  take_if(trail_all(rest), Parts{sp, name, neg, int, frac, rest})

def pl.frac.ok(ok: Bool, sp: String, name: String, neg: Bool, int: List<&2, Nat>, fs: List<&2, Nat>, rest: String) -> Maybe<&2, Parts>:
  match ok:
    case True{}:
      pl.trail(sp, name, neg, int, Some{fs}, rest)
    case False{}:
      None{}

def pl.frac.got(sp: String, name: String, neg: Bool, int: List<&2, Nat>, r: List<&2, Nat> & String) -> Maybe<&2, Parts>:
  (fs, rest) = r
  +f = fs
  pl.frac.ok(any_d(f), sp, name, neg, int, f, rest)

def pl.point(dot: Bool, sp: String, name: String, neg: Bool, int: List<&2, Nat>, c: Char, t: String) -> Maybe<&2, Parts>:
  match dot:
    case True{}:
      pl.frac.got(sp, name, neg, int, span_d(t))
    case False{}:
      pl.trail(sp, name, neg, int, None{}, SCon{c, t})

# after the integer digits: a point and the fraction's digits, or the end
def pl.frac(sp: String, name: String, neg: Bool, int: List<&2, Nat>, rest: String) -> Maybe<&2, Parts>:
  match rest:
    case SNil{}:
      Some{Parts{sp, name, neg, int, None{}, SNil{}}}
    case SCon{+c, t}:
      pl.point(same_char(c, '.'), sp, name, neg, int, c, t)

def pl.int.ok(ok: Bool, sp: String, name: String, neg: Bool, int: List<&2, Nat>, rest: String) -> Maybe<&2, Parts>:
  match ok:
    case True{}:
      pl.frac(sp, name, neg, int, rest)
    case False{}:
      None{}

def pl.int(sp: String, name: String, neg: Bool, r: List<&2, Nat> & String) -> Maybe<&2, Parts>:
  (ds, rest) = r
  +int = ds
  pl.int.ok(any_d(int), sp, name, neg, int, rest)

def pl.sign.at(minus: Bool, sp: String, name: String, c: Char, t: String) -> Maybe<&2, Parts>:
  match minus:
    case True{}:
      pl.int(sp, name, True{}, span_d(t))
    case False{}:
      pl.int(sp, name, False{}, span_d(SCon{c, t}))

# after '=': a '-' or not, then the integer digits
def pl.sign(sp: String, name: String, rest: String) -> Maybe<&2, Parts>:
  match rest:
    case SNil{}:
      None{}
    case SCon{+c, t}:
      pl.sign.at(same_char(c, '-'), sp, name, c, t)

def pl.eq.at(eq: Bool, sp: String, name: String, t: String) -> Maybe<&2, Parts>:
  match eq:
    case True{}:
      pl.sign(sp, name, t)
    case False{}:
      None{}

# after the name: '='
def pl.eq(sp: String, name: String, rest: String) -> Maybe<&2, Parts>:
  match rest:
    case SNil{}:
      None{}
    case SCon{c, t}:
      pl.eq.at(same_char(c, '='), sp, name, t)

def pl.name.ok(ok: Bool, sp: String, name: String, rest: String) -> Maybe<&2, Parts>:
  match ok:
    case True{}:
      pl.eq(sp, name, rest)
    case False{}:
      None{}

def pl.name(sp: String, r: String & String) -> Maybe<&2, Parts>:
  (nm, rest) = r
  +name = nm
  pl.name.ok(some(name), sp, name, rest)

def pl.sp.ok(ok: Bool, sp: String, rest: String) -> Maybe<&2, Parts>:
  match ok:
    case True{}:
      pl.name(sp, span_n(rest))
    case False{}:
      None{}

def pl.sp(r: String & String) -> Maybe<&2, Parts>:
  (b, rest) = r
  +sp = b
  pl.sp.ok(some(sp), sp, rest)

def pl.head(m: Maybe<&2, String>) -> Maybe<&2, Parts>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      pl.sp(span_b(r))

# the parts of a METRIC line, if s is one
def parse(s: String) -> Maybe<&2, Parts>:
  pl.head(prefix("METRIC", s))

# The value
# ---------

def strip.last(zero: Bool, x: Nat) -> List<&2, Nat>:
  match zero:
    case True{}:
      Nil{}
    case False{}:
      [x]

def strip.at(+x: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match r:
    case Nil{}:
      strip.last(Nat.is_eq(x, 0n), x)
    case y <> t:
      x <> (y <> t)

# xs without its trailing zeros
def strip(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      strip.at(x, strip(t))

def drop.at(zero: Bool, x: Nat, t: List<&2, Nat>, r: List<&2, Nat>) -> List<&2, Nat>:
  match zero:
    case True{}:
      r
    case False{}:
      x <> t

# xs without its leading zeros
def drop(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> +t:
      drop.at(Nat.is_eq(x, 0n), x, t, drop(t))

def frac_ds(f: Maybe<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match f:
    case None{}:
      Nil{}
    case Some{fs}:
      fs

def canon.fit(fit: Bool, n: String, neg: Bool, +ds: List<&2, Nat>, scale: Nat) -> Maybe<&2, Kv>:
  match fit:
    case True{}:
      Some{Kv{n, D.Dec{Bool.and(neg, any_d(ds)), ds, scale}}}
    case False{}:
      None{}

def canon.go(n: String, neg: Bool, int: List<&2, Nat>, +f: List<&2, Nat>) -> Maybe<&2, Kv>:
  +ds = drop(D.cat(int, f))
  canon.fit(Nat.is_le(D.len(ds), 15n), n, neg, ds, D.len(f))

# the name and canonical value the parts say, when the value has at most
# 15 significant digits
def canon(p: Parts) -> Maybe<&2, Kv>:
  match p:
    case Parts{sp, n, neg, int, frac, trail}:
      canon.go(n, neg, int, strip(frac_ds(frac)))

def metric.of(m: Maybe<&2, Parts>) -> Maybe<&2, Kv>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      canon(p)

# the metric a line reports, if it is a METRIC line
def metric(s: String) -> Maybe<&2, Kv>:
  metric.of(parse(s))
