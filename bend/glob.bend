# glob: the glob patterns eukhe matches paths and model names with (Rust:
# the `globset` crate 0.4.20 as eukhe used it: `GlobBuilder` with
# `backslash_escape` on, `empty_alternates` and `allow_unclosed_class`
# off, `literal_separator` and `case_insensitive` per caller). It runs as
# the compiled core (bend/ffi_glob.bend); laws/glob.bend states its laws.
#
# Three steps, as globset takes them:
# 1. `parse` reads a pattern into globset's tokens, char by char, with
#    globset's parser state (a stack of alternate branches) and its errors.
#    An alternate group `{a,b}` is expanded at once: a branch holds the
#    alternatives its groups spell out (each a token list), so no token
#    nests. A group branch whose regex would be empty is dropped, as
#    globset drops it (`{,a}` matches only `a`); a group with no branch
#    left matches the empty text.
# 2. `items` turns the tokens into globset's regex, as lists of byte
#    items: one byte of a class (`One`) or any run of bytes of a class
#    (`Star`). globset's regex reads bytes (`(?-u)`), so `?` and `[..]`
#    take one byte of the UTF-8 text, and a class with a non-ASCII char
#    holds that char's bytes as regex-syntax reads `\xNN` escapes.
#    `case_insensitive` folds ASCII letters only (`(?-u)(?i)`).
# 3. `matches` runs the items over the UTF-8 bytes of the text: the whole
#    text, one alternative at a time, by a table that holds, for each
#    suffix of the text, which suffixes of the items match it (time:
#    bytes x items per alternative; no backtracking).
# Pure: no IO, no @unsafe.

import Base

# Patterns
# --------

# the builder options a caller sets: `*`, `?` never match `/` (sep:
# globset's literal_separator); ASCII letters match either case (fold)
type Opts is Data:
  Opts{sep: Bool, fold: Bool}

# a range of chars in a class
type Rg is Data:
  Rg{lo: Char, hi: Char}

# globset's tokens (Alternates expanded away)
type Tok is Data:
  # the char itself
  TLit{c: Char}
  # `?`
  TAny{}
  # `*`
  TZom{}
  # `**/` at the start: `(?:/?|.*/)`
  TRPre{}
  # `/**` at the end: `/.*`
  TRSuf{}
  # `/**/`: `(?:/|/.*/)`
  TRZom{}
  # `[..]`, `[!..]`
  TCls{neg: Bool, rs: List<&2, Rg>}

# globset's parse errors
type Err is Data:
  # UnclosedClass
  EClass{}
  # InvalidRange(lo, hi)
  ERange{lo: Char, hi: Char}
  # UnopenedAlternates
  EUnopened{}
  # UnclosedAlternates
  EUnclosed{}
  # DanglingEscape
  EEscape{}

# a parsed pattern: its alternatives, and whether it is the lone token
# `**` (globset's regex `.*`)
type Glob is Data:
  Glob{alts: List<&2, List<&2, Tok>>, solo: Bool}

# Parser state
# ------------

# a branch being read: its alternatives (each token list holds its last
# token first), whether it holds a token, whether its regex is empty so
# far, whether its one token is a recursive prefix
type Br is Data:
  Br{alts: List<&2, List<&2, Tok>>, has: Bool, empty: Bool, solo: Bool}

# an open group: the branch it sits in, its finished branches (last first)
type Open is Data:
  Open{parent: Br, sibs: List<&2, Br>}

# what the next char continues
type Mode is Data:
  MNorm{}
  # after `\`
  MEsc{}
  # after one `*`; p: the char before it
  MStar1{p: Maybe<&2, Char>}
  # after `**`; p: the char before them
  MStar2{p: Maybe<&2, Char>}
  # after `[`
  MClsStart{}
  # inside a class: negated, its ranges (last first), at its first char,
  # after a `-` that opens a range
  MCls{neg: Bool, rs: List<&2, Rg>, first: Bool, inr: Bool}

type St is Data:
  St{cur: Br, outer: List<&2, Open>, prev: Maybe<&2, Char>, mode: Mode, bad: Maybe<&2, Err>}

def code(c: Char) -> U32:
  match c:
    case Chr{x}:
      x

def br0() -> Br:
  Br{[Nil{}], False{}, True{}, False{}}

def is_rpre(t: Tok) -> Bool:
  match t:
    case TRPre{}:
      True{}
    case TLit{c}:
      False{}
    case TAny{}:
      False{}
    case TZom{}:
      False{}
    case TRSuf{}:
      False{}
    case TRZom{}:
      False{}
    case TCls{n, r}:
      False{}

def cons_all(+t: Tok, xs: List<&2, List<&2, Tok>>) -> List<&2, List<&2, Tok>>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> r:
      (t <> a) <> cons_all(t, r)

# the token pushed onto the branch
def push(b: Br, +t: Tok) -> Br:
  match b:
    case Br{alts, has, empty, solo}:
      Br{cons_all(t, alts), True{}, False{}, Bool.and(Bool.not(has), is_rpre(t))}

def push2(b: Br, +t: Tok) -> Br:
  push(push(b, t), t)

# `**` after a separator: the last token goes; a recursive prefix or
# suffix stays, any other becomes a suffix (sfx) or a `/**/`
def swap_tok(t: Tok, sfx: Bool) -> Tok:
  match t:
    case TRPre{}:
      TRPre{}
    case TRSuf{}:
      TRSuf{}
    case TLit{c}:
      match sfx:
        case True{}:
          TRSuf{}
        case False{}:
          TRZom{}
    case TAny{}:
      match sfx:
        case True{}:
          TRSuf{}
        case False{}:
          TRZom{}
    case TZom{}:
      match sfx:
        case True{}:
          TRSuf{}
        case False{}:
          TRZom{}
    case TRZom{}:
      match sfx:
        case True{}:
          TRSuf{}
        case False{}:
          TRZom{}
    case TCls{n, r}:
      match sfx:
        case True{}:
          TRSuf{}
        case False{}:
          TRZom{}

def swap_new(sfx: Bool) -> Tok:
  match sfx:
    case True{}:
      TRSuf{}
    case False{}:
      TRZom{}

def swap_alts(xs: List<&2, List<&2, Tok>>, +sfx: Bool) -> List<&2, List<&2, Tok>>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> r:
      match a:
        case Nil{}:
          [swap_new(sfx)] <> swap_alts(r, sfx)
        case t <> k:
          (swap_tok(t, sfx) <> k) <> swap_alts(r, sfx)

def swap_last(b: Br, +sfx: Bool) -> Br:
  match b:
    case Br{alts, has, empty, solo}:
      Br{swap_alts(alts, sfx), has, empty, solo}

# the alternatives of the group's branches whose regex is not empty
def gather(bs: List<&2, Br>) -> List<&2, List<&2, Tok>>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> r:
      match b:
        case Br{alts, has, empty, solo}:
          match empty:
            case True{}:
              gather(r)
            case False{}:
              List.append(&2, List<&2, Tok>, alts, gather(r))

# the group's alternatives g after the alternative p (last token first)
def after_all(+p: List<&2, Tok>, g: List<&2, List<&2, Tok>>) -> List<&2, List<&2, Tok>>:
  match g:
    case Nil{}:
      Nil{}
    case a <> r:
      List.append(&2, Tok, a, p) <> after_all(p, r)

def cross(ps: List<&2, List<&2, Tok>>, +g: List<&2, List<&2, Tok>>) -> List<&2, List<&2, Tok>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> r:
      List.append(&2, List<&2, Tok>, after_all(p, g), cross(r, g))

def close.with(b: Br, g: List<&2, List<&2, Tok>>) -> Br:
  match b g:
    case Br{alts, has, empty, solo} Nil{}:
      Br{alts, True{}, empty, False{}}
    case Br{alts, has, empty, solo} x <> r:
      Br{cross(alts, x <> r), True{}, False{}, False{}}

# `}`: the group of branches bs (last first) closes into the parent
def close(parent: Br, bs: List<&2, Br>) -> Br:
  close.with(parent, gather(List.reverse(&2, Br, bs)))

def is_c(c: Char, +x: U32) -> Bool:
  match c:
    case Chr{y}:
      U32.is_eq(y, x)

def is_cm(m: Maybe<&2, Char>, +x: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      is_c(c, x)

def st_push(st: St, +t: Tok) -> St:
  match st:
    case St{cur, outer, prev, mode, bad}:
      St{push(cur, t), outer, prev, MNorm{}, bad}

def st_mode(st: St, m: Mode) -> St:
  match st:
    case St{cur, outer, prev, mode, bad}:
      St{cur, outer, prev, m, bad}

def st_fail(st: St, e: Err) -> St:
  match st:
    case St{cur, outer, prev, mode, bad}:
      St{cur, outer, prev, MNorm{}, Some{e}}

# `{`
def st_open(st: St) -> St:
  match st:
    case St{cur, outer, prev, mode, bad}:
      St{br0(), Open{cur, Nil{}} <> outer, prev, MNorm{}, bad}

# `}`
def st_close(st: St) -> St:
  match st:
    case St{cur, outer, prev, mode, bad}:
      match outer:
        case Nil{}:
          St{cur, Nil{}, prev, MNorm{}, Some{EUnopened{}}}
        case o <> r:
          match o:
            case Open{parent, sibs}:
              St{close(parent, cur <> sibs), r, prev, MNorm{}, bad}

# `,`: a literal outside a group, a new branch inside one
def st_comma(st: St) -> St:
  match st:
    case St{cur, outer, prev, mode, bad}:
      match outer:
        case Nil{}:
          St{push(cur, TLit{','}), Nil{}, prev, MNorm{}, bad}
        case o <> r:
          match o:
            case Open{parent, sibs}:
              St{br0(), Open{parent, cur <> sibs} <> r, prev, MNorm{}, bad}

# what a char outside any class, escape or star does
type K is Data:
  KStar{}
  KAny{}
  KCls{}
  KOpen{}
  KClose{}
  KComma{}
  KEsc{}
  KLit{}

def kind.g(b: Bool) -> K:
  match b:
    case True{}:
      KEsc{}
    case False{}:
      KLit{}

def kind.f(+x: U32, b: Bool) -> K:
  match b:
    case True{}:
      KComma{}
    case False{}:
      kind.g(U32.is_eq(x, 92))

def kind.e(+x: U32, b: Bool) -> K:
  match b:
    case True{}:
      KClose{}
    case False{}:
      kind.f(x, U32.is_eq(x, 44))

def kind.d(+x: U32, b: Bool) -> K:
  match b:
    case True{}:
      KOpen{}
    case False{}:
      kind.e(x, U32.is_eq(x, 125))

def kind.c(+x: U32, b: Bool) -> K:
  match b:
    case True{}:
      KCls{}
    case False{}:
      kind.d(x, U32.is_eq(x, 123))

def kind.b(+x: U32, b: Bool) -> K:
  match b:
    case True{}:
      KAny{}
    case False{}:
      kind.c(x, U32.is_eq(x, 91))

def kind.a(+x: U32, b: Bool) -> K:
  match b:
    case True{}:
      KStar{}
    case False{}:
      kind.b(x, U32.is_eq(x, 63))

# `*` `?` `[` `{` `}` `,` `\` or another char
def kind(+x: U32) -> K:
  kind.a(x, U32.is_eq(x, 42))

def norm.star(st: St) -> St:
  match st:
    case St{cur, outer, +prev, mode, bad}:
      St{cur, outer, prev, MStar1{prev}, bad}

def norm.k(st: St, c: Char, k: K) -> St:
  match k:
    case KStar{}:
      norm.star(st)
    case KAny{}:
      st_push(st, TAny{})
    case KCls{}:
      st_mode(st, MClsStart{})
    case KOpen{}:
      st_open(st)
    case KClose{}:
      st_close(st)
    case KComma{}:
      st_comma(st)
    case KEsc{}:
      st_mode(st, MEsc{})
    case KLit{}:
      st_push(st, TLit{c})

# a char outside any class, escape or star
def norm(st: St, +c: Char) -> St:
  norm.k(st, c, kind(code(c)))

# `**` read; nx: the char after it (None at the end). The state after the
# decision, and whether the decision took nx (a separator)
type Took is Data:
  Took{st: St, used: Bool}

def star2.ext(st: St, t: Bool) -> Took:
  match t:
    case True{}:
      Took{st, True{}}
    case False{}:
      Took{st, False{}}

def star2.sfx_other(cur: Br, outer: List<&2, Open>, prev: Maybe<&2, Char>, bad: Maybe<&2, Err>, closer: Bool) -> Took:
  match closer:
    case True{}:
      Took{St{swap_last(cur, True{}), outer, prev, MNorm{}, bad}, False{}}
    case False{}:
      Took{St{push2(cur, TZom{}), outer, prev, MNorm{}, bad}, False{}}

def star2.sfx_char(cur: Br, outer: List<&2, Open>, prev: Maybe<&2, Char>, bad: Maybe<&2, Err>, +c: Char, sl: Bool) -> Took:
  match sl:
    case True{}:
      Took{St{swap_last(cur, False{}), outer, prev, MNorm{}, bad}, True{}}
    case False{}:
      +o = outer
      star2.sfx_other(cur, o, prev, bad, Bool.and(Bool.or(is_c(c, 44), is_c(c, 125)), Bool.not(List.is_empty(&2, Open, o))))

# `**` after a separator (or a group's `{` or `,`): a suffix at the end or
# before a group's `,` or `}`; a `/**/` before a separator (taken); else
# two stars
def star2.suffix(st: St, nx: Maybe<&2, Char>) -> Took:
  match st:
    case St{cur, outer, prev, mode, bad}:
      match nx:
        case None{}:
          Took{St{swap_last(cur, True{}), outer, prev, MNorm{}, bad}, False{}}
        case Some{+c}:
          star2.sfx_char(cur, outer, prev, bad, c, is_c(c, 47))

def star2.lead_char(cur: Br, outer: List<&2, Open>, prev: Maybe<&2, Char>, bad: Maybe<&2, Err>, sl: Bool) -> Took:
  match sl:
    case True{}:
      Took{St{push(cur, TRPre{}), outer, prev, MNorm{}, bad}, True{}}
    case False{}:
      Took{St{push2(cur, TZom{}), outer, prev, MNorm{}, bad}, False{}}

# `**` first in its branch: a recursive prefix at the end or before a
# separator (taken); else two stars
def star2.lead(st: St, nx: Maybe<&2, Char>) -> Took:
  match st:
    case St{cur, outer, prev, mode, bad}:
      match nx:
        case None{}:
          Took{St{push(cur, TRPre{}), outer, prev, MNorm{}, bad}, False{}}
        case Some{+c}:
          star2.lead_char(cur, outer, prev, bad, is_c(c, 47))

def star2.mid.k(two: Bool, st: St, nx: Maybe<&2, Char>) -> Took:
  match two:
    case True{}:
      match st:
        case St{cur, outer, prev, mode, bad}:
          Took{St{push2(cur, TZom{}), outer, prev, MNorm{}, bad}, False{}}
    case False{}:
      star2.suffix(st, nx)

# `**` after a token: two stars unless after a separator, or after a
# group's `{` or `,`
def star2.mid(st: St, +p: Maybe<&2, Char>, nx: Maybe<&2, Char>) -> Took:
  match st:
    case St{cur, +outer, prev, mode, bad}:
      star2.mid.k(Bool.and(Bool.not(is_cm(p, 47)), Bool.or(List.is_empty(&2, Open, outer), Bool.not(Bool.or(is_cm(p, 44), is_cm(p, 123))))), St{cur, outer, prev, mode, bad}, nx)

def star2(st: St, p: Maybe<&2, Char>, nx: Maybe<&2, Char>) -> Took:
  match st:
    case St{cur, outer, prev, mode, bad}:
      match cur:
        case Br{alts, has, empty, solo}:
          match has:
            case True{}:
              star2.mid(St{Br{alts, True{}, empty, solo}, outer, prev, mode, bad}, p, nx)
            case False{}:
              star2.lead(St{Br{alts, False{}, empty, solo}, outer, prev, mode, bad}, nx)

def star2.go(t: Took, +c: Char) -> St:
  match t:
    case Took{st, used}:
      match used:
        case True{}:
          st
        case False{}:
          norm(st, c)

def star2.end(t: Took) -> St:
  match t:
    case Took{st, used}:
      st

# a class: its next char
def cls.ext.k(lo: Char, hi: Char, t: List<&2, Rg>, +c: Char, below: Bool) -> Maybe<&2, Err> & List<&2, Rg>:
  match below:
    case True{}:
      +l = lo
      (Some{ERange{l, c}}, Rg{l, hi} <> t)
    case False{}:
      (None{}, Rg{lo, c} <> t)

def cls.ext(rs: List<&2, Rg>, +c: Char) -> Maybe<&2, Err> & List<&2, Rg>:
  match rs:
    case Nil{}:
      (None{}, [Rg{c, c}])
    case r <> t:
      match r:
        case Rg{+lo, hi}:
          cls.ext.k(lo, hi, t, c, U32.is_lt(code(c), code(lo)))

def cls.ext_st(st: St, +neg: Bool, r: Maybe<&2, Err> & List<&2, Rg>) -> St:
  match r:
    case (e, rs):
      match e:
        case None{}:
          st_mode(st, MCls{neg, rs, False{}, False{}})
        case Some{x}:
          st_fail(st, x)

def cls.end(st: St, neg: Bool, rs: List<&2, Rg>, inr: Bool) -> St:
  match inr:
    case True{}:
      st_push(st, TCls{neg, List.reverse(&2, Rg, Rg{'-', '-'} <> rs)})
    case False{}:
      st_push(st, TCls{neg, List.reverse(&2, Rg, rs)})

def cls.other(st: St, +neg: Bool, rs: List<&2, Rg>, inr: Bool, +c: Char) -> St:
  match inr:
    case True{}:
      cls.ext_st(st, neg, cls.ext(rs, c))
    case False{}:
      st_mode(st, MCls{neg, Rg{c, c} <> rs, False{}, False{}})

def cls.dash(dash: Bool, first: Bool, inr: Bool, st: St, +neg: Bool, rs: List<&2, Rg>, c: Char) -> St:
  match dash:
    case True{}:
      match first:
        case True{}:
          st_mode(st, MCls{neg, Rg{'-', '-'} <> rs, False{}, False{}})
        case False{}:
          match inr:
            case True{}:
              cls.ext_st(st, neg, cls.ext(rs, '-'))
            case False{}:
              st_mode(st, MCls{neg, rs, False{}, True{}})
    case False{}:
      cls.other(st, neg, rs, inr, c)

def cls.k(close: Bool, first: Bool, st: St, +neg: Bool, rs: List<&2, Rg>, inr: Bool, +c: Char) -> St:
  match close:
    case True{}:
      match first:
        case True{}:
          st_mode(st, MCls{neg, Rg{']', ']'} <> rs, False{}, False{}})
        case False{}:
          cls.end(st, neg, rs, inr)
    case False{}:
      cls.dash(is_c(c, 45), first, inr, st, neg, rs, c)

# inside a class: `]` closes it (a char when first), `-` makes a range
# of the last char and the next (a char when first or last)
def cls(st: St, +neg: Bool, rs: List<&2, Rg>, first: Bool, inr: Bool, +c: Char) -> St:
  cls.k(is_c(c, 93), first, st, neg, rs, inr, c)

def cls_start.k(st: St, +c: Char, bang: Bool) -> St:
  match bang:
    case True{}:
      st_mode(st, MCls{True{}, Nil{}, True{}, False{}})
    case False{}:
      cls(st, False{}, Nil{}, True{}, False{}, c)

# after `[`: `!` or `^` negates the class
def cls_start(st: St, +c: Char) -> St:
  cls_start.k(st, c, Bool.or(is_c(c, 33), is_c(c, 94)))

def star1.k(st: St, +p: Maybe<&2, Char>, +c: Char, two: Bool) -> St:
  match two:
    case True{}:
      st_mode(st, MStar2{p})
    case False{}:
      norm(st_push(st, TZom{}), c)

# one char of the pattern, by the mode it continues
def step.mode(st: St, m: Mode, +c: Char) -> St:
  match m:
    case MNorm{}:
      norm(st, c)
    case MEsc{}:
      st_push(st, TLit{c})
    case MStar1{+p}:
      star1.k(st, p, c, is_c(c, 42))
    case MStar2{p}:
      star2.go(star2(st, p, Some{c}), c)
    case MClsStart{}:
      cls_start(st, c)
    case MCls{neg, rs, first, inr}:
      cls(st, neg, rs, first, inr, c)

def step.set_prev(st: St, +c: Char) -> St:
  match st:
    case St{cur, outer, prev, mode, bad}:
      St{cur, outer, Some{c}, mode, bad}

def step(st: St, +c: Char) -> St:
  match st:
    case St{cur, outer, prev, mode, bad}:
      match bad:
        case Some{e}:
          St{cur, outer, prev, mode, Some{e}}
        case None{}:
          step.set_prev(step.mode(St{cur, outer, prev, MNorm{}, None{}}, mode, c), c)

def go(s: String, st: St) -> St:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      go(t, step(st, c))

# the pattern's end: what the open mode leaves
def fin.mode(st: St, m: Mode) -> St:
  match m:
    case MNorm{}:
      st
    case MEsc{}:
      st_fail(st, EEscape{})
    case MStar1{p}:
      st_push(st, TZom{})
    case MStar2{p}:
      star2.end(star2(st, p, None{}))
    case MClsStart{}:
      st_fail(st, EClass{})
    case MCls{neg, rs, first, inr}:
      st_fail(st, EClass{})

def fin.rev(xs: List<&2, List<&2, Tok>>) -> List<&2, List<&2, Tok>>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> r:
      List.reverse(&2, Tok, a) <> fin.rev(r)

def fin.ok(outer: List<&2, Open>, cur: Br) -> Result<&2, &2, Err, Glob>:
  match outer:
    case Nil{}:
      match cur:
        case Br{alts, has, empty, solo}:
          Done{Glob{fin.rev(alts), solo}}
    case o <> r:
      Fail{EUnclosed{}}

def fin.bad(bad: Maybe<&2, Err>, outer: List<&2, Open>, cur: Br) -> Result<&2, &2, Err, Glob>:
  match bad:
    case Some{e}:
      Fail{e}
    case None{}:
      fin.ok(outer, cur)

def fin.done(st: St) -> Result<&2, &2, Err, Glob>:
  match st:
    case St{cur, outer, prev, mode, bad}:
      fin.bad(bad, outer, cur)

def fin(st: St) -> Result<&2, &2, Err, Glob>:
  match st:
    case St{cur, outer, prev, mode, bad}:
      match bad:
        case Some{e}:
          Fail{e}
        case None{}:
          fin.done(fin.mode(St{cur, outer, prev, MNorm{}, None{}}, mode))

# the pattern's tokens, or globset's error
def parse(s: String) -> Result<&2, &2, Err, Glob>:
  fin(go(s, St{br0(), Nil{}, None{}, MNorm{}, None{}}))

# Items
# -----

# a range of bytes
type BR is Data:
  BR{lo: U32, hi: U32}

# a class of bytes
type BC is Data:
  # every byte (regex `.`: globset sets dot_matches_new_line)
  BAny{}
  # every byte but `/` (`[^/]`)
  BNotSl{}
  # the bytes of the ranges (none of them when negated); with fold, an
  # ASCII letter of either case
  BSet{neg: Bool, fold: Bool, rs: List<&2, BR>}

type It is Data:
  One{k: BC}
  Star{k: BC}

def utf8.d(+x: U32, rest: List<&2, U32>, b: Bool) -> List<&2, U32>:
  match b:
    case True{}:
      U32.or(224, U32.shrn(x, 12n)) <> U32.or(128, U32.and(U32.shrn(x, 6n), 63)) <> U32.or(128, U32.and(x, 63)) <> rest
    case False{}:
      U32.or(240, U32.shrn(x, 18n)) <> U32.or(128, U32.and(U32.shrn(x, 12n), 63)) <> U32.or(128, U32.and(U32.shrn(x, 6n), 63)) <> U32.or(128, U32.and(x, 63)) <> rest

def utf8.c(+x: U32, rest: List<&2, U32>, b: Bool) -> List<&2, U32>:
  match b:
    case True{}:
      U32.or(192, U32.shrn(x, 6n)) <> U32.or(128, U32.and(x, 63)) <> rest
    case False{}:
      utf8.d(x, rest, U32.is_lt(x, 65536))

def utf8.b(+x: U32, rest: List<&2, U32>, b: Bool) -> List<&2, U32>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      utf8.c(x, rest, U32.is_lt(x, 2048))

# the UTF-8 bytes of the char of code x, before rest
def utf8(+x: U32, rest: List<&2, U32>) -> List<&2, U32>:
  utf8.b(x, rest, U32.is_lt(x, 128))

# the UTF-8 bytes of a text
def bytes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      utf8(code(c), bytes(t))

def lit.go(bs: List<&2, U32>, +fold: Bool) -> List<&2, It>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      One{BSet{False{}, fold, [BR{b, b}]}} <> lit.go(r, fold)

# each byte as a range of itself, before rest
def singles(bs: List<&2, U32>, rest: List<&2, BR>) -> List<&2, BR>:
  match bs:
    case Nil{}:
      rest
    case +b <> r:
      BR{b, b} <> singles(r, rest)

def split_last.cons(b: U32, p: List<&2, U32> & U32) -> List<&2, U32> & U32:
  match p:
    case (i, l):
      (b <> i, l)

# a non-empty byte list: all but the last, and the last
def split_last(r: List<&2, U32>, b: U32) -> List<&2, U32> & U32:
  match r:
    case Nil{}:
      (Nil{}, b)
    case c <> t:
      split_last.cons(b, split_last(t, c))

def rg.mid(a: List<&2, U32> & U32, hb: List<&2, U32>, rest: List<&2, BR>) -> List<&2, BR>:
  match a hb:
    case (i, +l) Nil{}:
      singles(i, BR{l, l} <> rest)
    case (i, l) h <> t:
      singles(i, BR{l, h} <> singles(t, rest))

def rg.multi(bs: List<&2, U32>, +hi: U32, rest: List<&2, BR>) -> List<&2, BR>:
  match bs:
    case Nil{}:
      rest
    case b <> r:
      rg.mid(split_last(r, b), utf8(hi, Nil{}), rest)

def rg.k(+lo: U32, +hi: U32, rest: List<&2, BR>, same: Bool) -> List<&2, BR>:
  match same:
    case True{}:
      singles(utf8(lo, Nil{}), rest)
    case False{}:
      rg.multi(utf8(lo, Nil{}), hi, rest)

# the regex class items of the range lo..hi: lo's bytes, then a `-`
# between lo's last byte and hi's first, then hi's other bytes; one char
# alone is its bytes
def rg.bytes(+lo: U32, +hi: U32, rest: List<&2, BR>) -> List<&2, BR>:
  rg.k(lo, hi, rest, U32.is_eq(lo, hi))

def rgs(rs: List<&2, Rg>) -> List<&2, BR>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Rg{lo, hi}:
          rg.bytes(code(lo), code(hi), rgs(t))

def slash() -> It:
  One{BSet{False{}, False{}, [BR{47, 47}]}}

def one_or_star(sep: Bool, star: Bool) -> It:
  match sep star:
    case True{} True{}:
      Star{BNotSl{}}
    case True{} False{}:
      One{BNotSl{}}
    case False{} True{}:
      Star{BAny{}}
    case False{} False{}:
      One{BAny{}}

# the alternatives of globset's regex of one token
def tok(o: Opts, t: Tok) -> List<&2, List<&2, It>>:
  match o:
    case Opts{sep, +fold}:
      match t:
        case TLit{c}:
          [lit.go(utf8(code(c), Nil{}), fold)]
        case TAny{}:
          [[one_or_star(sep, False{})]]
        case TZom{}:
          [[one_or_star(sep, True{})]]
        case TRPre{}:
          [Nil{}, [slash()], [Star{BAny{}}, slash()]]
        case TRSuf{}:
          [[slash(), Star{BAny{}}]]
        case TRZom{}:
          [[slash()], [slash(), Star{BAny{}}, slash()]]
        case TCls{neg, rs}:
          [[One{BSet{neg, fold, rgs(rs)}}]]

def seq.pre(+a: List<&2, It>, bs: List<&2, List<&2, It>>) -> List<&2, List<&2, It>>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> r:
      List.append(&2, It, a, b) <> seq.pre(a, r)

def seq.cross(as: List<&2, List<&2, It>>, +bs: List<&2, List<&2, It>>) -> List<&2, List<&2, It>>:
  match as:
    case Nil{}:
      Nil{}
    case a <> r:
      List.append(&2, List<&2, It>, seq.pre(a, bs), seq.cross(r, bs))

# the alternatives of one token list: each token's alternatives in turn
def seq(+o: Opts, ts: List<&2, Tok>) -> List<&2, List<&2, It>>:
  match ts:
    case Nil{}:
      [Nil{}]
    case t <> r:
      seq.cross(tok(o, t), seq(o, r))

def alts(+o: Opts, xs: List<&2, List<&2, Tok>>) -> List<&2, List<&2, It>>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> r:
      List.append(&2, List<&2, It>, seq(o, a), alts(o, r))

# globset's regex of the pattern, as alternatives of byte items
def items(o: Opts, g: Glob) -> List<&2, List<&2, It>>:
  match g:
    case Glob{xs, solo}:
      match solo:
        case True{}:
          [[Star{BAny{}}]]
        case False{}:
          alts(o, xs)

# Matching
# --------

def in_rs(rs: List<&2, BR>, +x: U32) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case BR{lo, hi}:
          Bool.or(Bool.and(U32.is_le(lo, x), U32.is_le(x, hi)), in_rs(t, x))

def swap.lo(+x: U32, b: Bool) -> U32:
  match b:
    case True{}:
      U32.sub(x, 32)
    case False{}:
      x

def swap.up(+x: U32, b: Bool) -> U32:
  match b:
    case True{}:
      U32.add(x, 32)
    case False{}:
      swap.lo(x, Bool.and(U32.is_le(97, x), U32.is_le(x, 122)))

# the other case of an ASCII letter; any other byte itself
def swap(+x: U32) -> U32:
  swap.up(x, Bool.and(U32.is_le(65, x), U32.is_le(x, 90)))

def in_set(+rs: List<&2, BR>, +x: U32, fold: Bool) -> Bool:
  match fold:
    case True{}:
      Bool.or(in_rs(rs, x), in_rs(rs, swap(x)))
    case False{}:
      in_rs(rs, x)

# whether the byte x is of the class k
def bc(k: BC, +x: U32) -> Bool:
  match k:
    case BAny{}:
      True{}
    case BNotSl{}:
      Bool.not(U32.is_eq(x, 47))
    case BSet{neg, fold, rs}:
      match neg:
        case True{}:
          Bool.not(in_set(rs, x, fold))
        case False{}:
          in_set(rs, x, fold)

def hd(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case b <> r:
      b

# the row of the empty text: for each suffix of the items (the whole
# list first, the empty one last), whether it matches the empty text
def nul(its: List<&2, It>) -> List<&2, Bool>:
  match its:
    case Nil{}:
      [True{}]
    case i <> k:
      match i:
        case One{c}:
          False{} <> nul(k)
        case Star{c}:
          +r = nul(k)
          hd(r) <> r

def row.cons(i: It, +x: U32, p: Bool, +pr: List<&2, Bool>, +rest: List<&2, Bool>) -> List<&2, Bool>:
  match i:
    case One{c}:
      Bool.and(bc(c, x), hd(pr)) <> rest
    case Star{c}:
      Bool.or(hd(rest), Bool.and(bc(c, x), p)) <> rest

# the row of the text x <> t from prev, the row of t: the items i <> k
# match x <> t when i takes x and k matches t (One), or k matches x <> t
# or i takes x and i <> k matches t (Star)
def row(its: List<&2, It>, +x: U32, prev: List<&2, Bool>) -> List<&2, Bool>:
  match its:
    case Nil{}:
      [False{}]
    case i <> k:
      match prev:
        case Nil{}:
          [False{}]
        case p <> +pr:
          row.cons(i, x, p, pr, row(k, x, pr))

# for each suffix of the items, whether it matches the whole byte text
def rows(bs: List<&2, U32>, +its: List<&2, It>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      nul(its)
    case x <> t:
      row(its, x, rows(t, its))

# whether the items match the whole byte text
def full(+bs: List<&2, U32>, its: List<&2, It>) -> Bool:
  hd(rows(bs, its))

# hit, else the rest (the rest runs only on a miss)
def or_else(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether one of the alternatives matches the whole byte text
def any_full(+bs: List<&2, U32>, xs: List<&2, List<&2, It>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case a <> r:
      or_else(full(bs, a), u => any_full(bs, r))

# whether the parsed pattern matches the whole text
def matches(o: Opts, g: Glob, s: String) -> Bool:
  any_full(bytes(s), items(o, g))

# Queries
# -------

# the error of a pattern globset refuses
def check.r(r: Result<&2, &2, Err, Glob>) -> Maybe<&2, Err>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{g}:
      None{}

def check(p: String) -> Maybe<&2, Err>:
  check.r(parse(p))

def compile.r(+o: Opts, r: Result<&2, &2, Err, Glob>, rest: List<&2, List<&2, It>>) -> List<&2, List<&2, It>>:
  match r:
    case Fail{e}:
      rest
    case Done{g}:
      List.append(&2, List<&2, It>, items(o, g), rest)

# the alternatives of every pattern globset accepts (a refused pattern
# matches nothing)
def compile(+o: Opts, ps: List<&2, String>) -> List<&2, List<&2, It>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> r:
      compile.r(o, parse(p), compile(o, r))

# whether one of the texts ss matches one of the alternatives xs
def hit_any(ss: List<&2, String>, +xs: List<&2, List<&2, It>>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case s <> r:
      or_else(any_full(bytes(s), xs), u => hit_any(r, xs))

# the texts ss in groups of the sizes ks, in order: whether a pattern
# matches a text of each group (a group past the texts takes those left)
def groups(ks: List<&2, Nat>, +xs: List<&2, List<&2, It>>, +ss: List<&2, String>) -> List<&2, Bool>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> r:
      hit_any(List.take(&2, String, ss, k), xs) <> groups(r, xs, List.drop(&2, String, ss, k))

# each group of texts: whether one of the patterns ps matches one of its
# texts
def match_groups(+o: Opts, ps: List<&2, String>, ss: List<&2, String>, ks: List<&2, Nat>) -> List<&2, Bool>:
  groups(ks, compile(o, ps), ss)

# per rule of the sizes ks (its patterns in order: a rule past the
# patterns takes those left), whether one of its patterns matches one of
# the texts ss
def rules(ks: List<&2, Nat>, +o: Opts, +ps: List<&2, String>, +ss: List<&2, String>) -> List<&2, Bool>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> r:
      hit_any(ss, compile(o, List.take(&2, String, ps, k))) <> rules(r, o, List.drop(&2, String, ps, k), ss)

# Ignore rules
# ------------

# an ignore rule: a glob (literal separators) matched against the whole
# path (anchored) or any of its `/`-suffixes, negated (a match keeps the
# path), for directories only; every path under a prefix; a rule of an
# unknown code, which decides nothing
type IR is Data:
  IGlob{xs: List<&2, List<&2, It>>, anchored: Bool, negated: Bool, dir_only: Bool}
  IAll{prefix: String}
  ISkip{}

# the rule of the text p and the code c: 0-7 a glob (bit 1 anchored,
# bit 2 negated, bit 4 directories only), 8 every path under the prefix
# p, any other nothing
def ir(p: String, c: Nat) -> IR:
  match c:
    case 0n:
      IGlob{compile(Opts{True{}, False{}}, [p]), False{}, False{}, False{}}
    case 1n:
      IGlob{compile(Opts{True{}, False{}}, [p]), True{}, False{}, False{}}
    case 2n:
      IGlob{compile(Opts{True{}, False{}}, [p]), False{}, True{}, False{}}
    case 3n:
      IGlob{compile(Opts{True{}, False{}}, [p]), True{}, True{}, False{}}
    case 4n:
      IGlob{compile(Opts{True{}, False{}}, [p]), False{}, False{}, True{}}
    case 5n:
      IGlob{compile(Opts{True{}, False{}}, [p]), True{}, False{}, True{}}
    case 6n:
      IGlob{compile(Opts{True{}, False{}}, [p]), False{}, True{}, True{}}
    case 7n:
      IGlob{compile(Opts{True{}, False{}}, [p]), True{}, True{}, True{}}
    case 8n:
      IAll{p}
    case 9n+k:
      ISkip{}

# the rules of the texts ps and codes cs, paired in order (the shorter
# list ends them), last rule first
def irs(ps: List<&2, String>, cs: List<&2, Nat>, acc: List<&2, IR>) -> List<&2, IR>:
  match ps cs:
    case Nil{} cs:
      acc
    case p <> pr Nil{}:
      acc
    case p <> pr c <> cr:
      irs(pr, cr, ir(p, c) <> acc)

# the texts after each `/` of s
def after_slashes.k(sl: Bool, t: String, rest: List<&2, String>) -> List<&2, String>:
  match sl:
    case True{}:
      t <> rest
    case False{}:
      rest

def after_slashes(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, +t}:
      after_slashes.k(is_c(c, 47), t, after_slashes(t))

def glob_hit(anchored: Bool, +path: String, +xs: List<&2, List<&2, It>>) -> Bool:
  match anchored:
    case True{}:
      any_full(bytes(path), xs)
    case False{}:
      hit_any(path <> after_slashes(path), xs)

def decide.hit(hit: Bool, negated: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      Bool.not(negated)
    case False{}:
      rest(Unit{})

def decide.glob(skip: Bool, xs: List<&2, List<&2, It>>, anchored: Bool, negated: Bool, +path: String, rest: Unit -> Bool) -> Bool:
  match skip:
    case True{}:
      rest(Unit{})
    case False{}:
      decide.hit(glob_hit(anchored, path, xs), negated, rest)

def decide.all(under: Bool, rest: Unit -> Bool) -> Bool:
  match under:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# rule r on the path (dir: a directory), else the rules after it
def decide.r(r: IR, +path: String, +dir: Bool, rest: Unit -> Bool) -> Bool:
  match r:
    case IGlob{xs, anchored, negated, dir_only}:
      decide.glob(Bool.and(dir_only, Bool.not(dir)), xs, anchored, negated, path, rest)
    case IAll{prefix}:
      decide.all(String.starts_with(path, prefix), rest)
    case ISkip{}:
      rest(Unit{})

# whether the rules rs (last rule first) ignore the path: the first rule
# that decides it, else not ignored
def decide(rs: List<&2, IR>, +path: String, +dir: Bool) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      decide.r(r, path, dir, u => decide(t, path, dir))

def split_dir.cons(+c: Char, r: String & Bool) -> String & Bool:
  match r:
    case (t, d):
      (SCon{c, t}, d)

def split_dir.last(+c: Char, sl: Bool) -> String & Bool:
  match sl:
    case True{}:
      ("", True{})
    case False{}:
      (SCon{c, SNil{}}, False{})

# an entry as Rust sends it: its path, a directory's with one `/` after
# it; the path without that `/`, and whether it is a directory
def split_dir(s: String) -> String & Bool:
  match s:
    case SNil{}:
      ("", False{})
    case SCon{+c, t}:
      match t:
        case SNil{}:
          split_dir.last(c, is_c(c, 47))
        case SCon{x, u}:
          split_dir.cons(c, split_dir(SCon{x, u}))

def ignored.e(+rs: List<&2, IR>, e: String & Bool) -> Bool:
  match e:
    case (+path, +dir):
      decide(rs, path, dir)

def ignored.go(es: List<&2, String>, +rs: List<&2, IR>) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case e <> r:
      ignored.e(rs, split_dir(e)) <> ignored.go(r, rs)

# for each entry, whether the ignore rules (the texts ps with the codes cs,
# in the order the ignore files give them) ignore it
def ignored(ps: List<&2, String>, cs: List<&2, Nat>, es: List<&2, String>) -> List<&2, Bool>:
  ignored.go(es, irs(ps, cs, Nil{}))

# The model allowlist
# -------------------

# Unicode White_Space (Rust `char::is_whitespace`, `str::trim`)
def ws(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

def trim_start.k(w: Bool, c: Char, t: String, rest: String) -> String:
  match w:
    case True{}:
      rest
    case False{}:
      SCon{c, t}

# s without its leading white space
def trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      trim_start.k(ws(c), c, t, trim_start(t))

# s without its leading and trailing white space (Rust `str::trim`)
def trim(s: String) -> String:
  String.reverse(trim_start(String.reverse(trim_start(s))))

# s holds `*`, `?` or `[` (the allowlist's test for a glob)
def wild(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          Bool.or(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), U32.is_eq(x, 91))), wild(t))

def after_slash.k(sl: Bool, t: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match sl:
    case True{}:
      Some{t}
    case False{}:
      rest

# the text after the first `/` of s
def after_slash(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, +t}:
      after_slash.k(is_c(c, 47), t, after_slash(t))

def bare.k(s: String, m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      s
    case Some{t}:
      t

# the bare id of a selector: the text after its first `/` (prime-inference
# ids carry more slashes); the selector itself with none
def bare(+s: String) -> String:
  bare.k(s, after_slash(s))

def allow.g(r: Result<&2, &2, Err, Glob>, +sel: String) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{g}:
      hit_any([sel, bare(sel)], items(Opts{False{}, False{}}, g))

def allow.w(w: Bool, +sel: String, +p: String) -> Bool:
  match w:
    case True{}:
      allow.g(parse(p), sel)
    case False{}:
      Bool.or(String.eq(p, sel), String.eq(p, bare(sel)))

def allow.e(e: Bool, +sel: String, +p: String) -> Bool:
  match e:
    case True{}:
      False{}
    case False{}:
      allow.w(wild(p), sel, p)

def allow.t(+sel: String, +p: String) -> Bool:
  allow.e(String.is_empty(p), sel, p)

# one allowlist pattern (lowercase) against a selector (lowercase): its
# trimmed text, blank never matches; with `*`, `?` or `[` a glob (globset
# defaults: `*` crosses `/`; a refused glob matches nothing) of the whole
# selector or its bare id; else equal to one of them
def allow1(+sel: String, p: String) -> Bool:
  allow.t(sel, trim(p))

# whether the allowlist ps allows the selector (an empty list allows
# nothing)
def allowed(+sel: String, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> r:
      or_else(allow1(sel, p), u => allowed(sel, r))
