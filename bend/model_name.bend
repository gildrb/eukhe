# model_name: the explicit name rules of the quirks rulebook (eukhe-ai
# quirks/rulebook.json: each family's `match` and `except` sets and the
# price rows' name rules) and the separator rule of its match candidates.
# Each rule is a plain string test (a prefix taken off, a part searched, a
# run of digits read); laws/model_name.bend states each in plain words over
# splits of the name. Above each rule: the regexes it replaced. Pure: no
# IO, no @unsafe.

import Base
import ./text_pat.bend as Tp
import ./phrase.bend as P

# One rule over a name
type Rule is Data:
  # the name holds one of ps as a part
  RContains{ps: List<&2, String>}
  # the name is one of ps
  RIs{ps: List<&2, String>}
  # the name begins with one of ps
  RStarts{ps: List<&2, String>}
  # the name holds a, and after it, on the same line, b
  RThen{a: String, b: String}
  # the name begins with one of `after`, then a number (see num.on)
  RNumber{after: List<&2, String>, least: Nat, whole: Bool}
  # the part of the name after its last `/` begins with one of ps
  RSegment{ps: List<&2, String>}

# Text
# ----

# t when b, else f
def ite(b: Bool, t: Unit -> Bool, f: Unit -> Bool) -> Bool:
  match b:
    case True{}:
      t(Unit{})
    case False{}:
      f(Unit{})

def strip.go(ok: Bool, rest: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      rest(Unit{})
    case False{}:
      None{}

# s after p, when s begins with p
def strip(p: String, s: String) -> Maybe<&2, String>:
  match p:
    case SNil{}:
      Some{s}
    case SCon{c, pt}:
      match s:
        case SNil{}:
          None{}
        case SCon{x, st}:
          strip.go(Char.is_eq(c, x), u => strip(pt, st))

# a rest was found
def got(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      True{}

# a rest was found and it is empty
def got_all(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      String.is_empty(r)

# The rules
# ---------

# R1: whether s holds p as a part (some suffix of s begins with p)
def part(+p: String, s: String) -> Bool:
  match s:
    case SNil{}:
      got(strip(p, SNil{}))
    case SCon{+x, +t}:
      P.pm.or(got(strip(p, SCon{x, t})), u => part(p, t))

# R1 contains: opus-4-7|opus-4-8|opus-5|sonnet-5|haiku-5|fable-5, 2\.5-flash,
# gemma-?4, claude (a part of the name, anywhere)
def parts(ps: List<&2, String>, +s: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> more:
      P.pm.or(part(p, s), u => parts(more, s))

# R2 is: ^(?:gpt-5\.6|gpt-6-astra)$, ^gemini-flash(?:-lite)?-latest$,
# ^grok-4\.[67]$ (the whole name)
def iss(ps: List<&2, String>, +s: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> more:
      P.pm.or(got_all(strip(p, s)), u => iss(more, s))

# R3 starts: ^gpt-5\.6- (the name's start)
def heads(ps: List<&2, String>, +s: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> more:
      P.pm.or(got(strip(p, s)), u => heads(more, s))

# whether b is a part of s that starts before the first line feed of s
def line_part(+b: String, s: String) -> Bool:
  match s:
    case SNil{}:
      got(strip(b, SNil{}))
    case SCon{+x, +t}:
      P.pm.or(got(strip(b, SCon{x, t})), u => P.pm.and(Bool.not(Char.is_eq(x, '\n')), v => line_part(b, t)))

def then.at(m: Maybe<&2, String>, +b: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      line_part(b, r)

# R4 then: claude.*-4-|-4-.*claude (`.` takes no line feed): some place of
# s begins with a, and b follows on the same line
def then(+a: String, +b: String, s: String) -> Bool:
  match s:
    case SNil{}:
      then.at(strip(a, SNil{}), b)
    case SCon{+x, +t}:
      P.pm.or(then.at(strip(a, SCon{x, t}), b), u => then(a, b, t))

# the value of a digit char
def digit(c: Char) -> Nat:
  Nat.sub(U32.to_nat(Char.to_u32(c)), 48n)

def drop0.at(z: Bool, s: String, rest: Unit -> String) -> String:
  match z:
    case True{}:
      rest(Unit{})
    case False{}:
      s

# s without its leading `0`s
def drop0(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+x, +t}:
      drop0.at(Char.is_eq(x, '0'), SCon{x, t}, u => drop0(t))

# x follows the digits: with whole, only a `-` may
def num.end(whole: Bool, x: Char) -> Bool:
  match whole:
    case True{}:
      Char.is_eq(x, '-')
    case False{}:
      True{}

# past two significant digits: more digits, then the end
def num.rest(s: String, +whole: Bool) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+x, t}:
      ite(Tp.is_dig(x), u => num.rest(t, whole), v => num.end(whole, x))

# past one significant digit (ok: its value is at least the least)
def num.second(s: String, ok: Bool, +whole: Bool) -> Bool:
  match s:
    case SNil{}:
      ok
    case SCon{+x, t}:
      ite(Tp.is_dig(x), u => num.rest(t, whole), v => Bool.and(ok, num.end(whole, x)))

# the first significant digit (s has no leading `0`)
def num.first(s: String, +least: Nat, +whole: Bool) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+x, t}:
      ite(Tp.is_dig(x), u => num.second(t, Nat.is_le(least, digit(x)), whole), v => False{})

# the number after a prefix: the run of digits there, without its leading
# zeros, has two or more digits, or one not below the least; with whole,
# the name ends after the run or a `-` follows it
def num.on(m: Maybe<&2, String>, +least: Nat, +whole: Bool) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      num.first(drop0(r), least, whole)

# R5 number: ^gemini(?:-live)?-0*(?:[3-9]|[1-9][0-9]+),
# ^gpt-6(?:$|[-.])|^gpt-5\.0*(?:[6-9]|[1-9][0-9]+)(?:$|-)
def nums(ps: List<&2, String>, +s: String, +least: Nat, +whole: Bool) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> more:
      P.pm.or(num.on(strip(p, s), least, whole), u => nums(more, s, least, whole))

def seg.at(slash: Bool, t: String, at: String) -> String:
  match slash:
    case True{}:
      t
    case False{}:
      at

# the part of s after its last `/` (at: the part after the last `/` read
# so far, from the start)
def seg.go(s: String, at: String) -> String:
  match s:
    case SNil{}:
      at
    case SCon{x, +t}:
      seg.go(t, seg.at(Char.is_eq(x, '/'), t, at))

# R6 segment_starts: (?:^|/)(?:qwen|qwq)[^/]*$
def seg(+s: String) -> String:
  seg.go(s, s)

# whether the rule r holds for the name s
def rule(r: Rule, +s: String) -> Bool:
  match r:
    case RContains{ps}:
      parts(ps, s)
    case RIs{ps}:
      iss(ps, s)
    case RStarts{ps}:
      heads(ps, s)
    case RThen{a, b}:
      then(a, b, s)
    case RNumber{ps, n, w}:
      nums(ps, s, n, w)
    case RSegment{ps}:
      heads(ps, seg(s))

# R7: sets and groups
# ------------------

# whether one rule of rs holds for the name s
def rules(rs: List<&2, Rule>, +s: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> more:
      P.pm.or(rule(r, s), u => rules(more, s))

# whether one rule of rs holds for one name of g
def set_holds(+rs: List<&2, Rule>, g: List<&2, String>) -> Bool:
  match g:
    case Nil{}:
      False{}
    case s <> more:
      P.pm.or(rules(rs, s), u => set_holds(rs, more))

# for each set, whether it holds for the group g, then rest
def row(sets: List<&2, List<&2, Rule>>, +g: List<&2, String>, rest: List<&2, Bool>) -> List<&2, Bool>:
  match sets:
    case Nil{}:
      rest
    case rs <> more:
      set_holds(rs, g) <> row(more, g, rest)

# for each group in order, for each set in order: whether the set holds for
# the group
def holds(+sets: List<&2, List<&2, Rule>>, groups: List<&2, List<&2, String>>) -> List<&2, Bool>:
  match groups:
    case Nil{}:
      Nil{}
    case g <> more:
      row(sets, g, holds(sets, more))

# R8: dash
# --------

# a separator: a Unicode White_Space char, `_`, `.` or `:`
def is_sep(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Tp.is_ws(Chr{x}), Bool.or(U32.is_eq(x, 95), Bool.or(U32.is_eq(x, 46), U32.is_eq(x, 58))))

def dash.at(sep: Bool, run: Bool, c: Char, rest: Bool -> String) -> String:
  match sep:
    case True{}:
      match run:
        case True{}:
          rest(True{})
        case False{}:
          SCon{'-', rest(True{})}
    case False{}:
      SCon{c, rest(False{})}

# s with each maximal run of separators replaced by one `-` (run: the char
# before s was a separator)
def dash.go(s: String, run: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      dash.at(is_sep(c), run, c, r => dash.go(t, r))

# [\s_.:]+ replaced by `-`
def dash(s: String) -> String:
  dash.go(s, False{})

def dashes(ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> more:
      dash(t) <> dashes(more)
