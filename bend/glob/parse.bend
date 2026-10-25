# glob/parse: globset's pattern parser (step 1 of bend/glob/): a pattern
# read char by char into globset's tokens, with globset's parser state
# (a stack of alternate branches) and its errors. An alternate group
# `{a,b}` is expanded at once: a branch holds the alternatives its groups
# spell out (each a token list), so no token nests. A group branch whose
# regex would be empty is dropped, as globset drops it (`{,a}` matches
# only `a`); a group with no branch left matches the empty text.
#
# bend/glob/ is the glob patterns eukhe matches paths and model names
# with (Rust: the `globset` crate 0.4.20 as eukhe used it: `GlobBuilder`
# with `backslash_escape` on, `empty_alternates` and
# `allow_unclosed_class` off, `literal_separator` and `case_insensitive`
# per caller). It runs as the compiled core (bend/ffi_glob.bend);
# laws/glob.bend states its laws. Pure: no IO, no @unsafe.

import Base

# Patterns
# --------

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
