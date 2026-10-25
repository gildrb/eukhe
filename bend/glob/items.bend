# glob/items: globset's regex of parsed tokens (step 2 of bend/glob/), as
# lists of byte items: one byte of a class (`One`) or any run of bytes of
# a class (`Star`). globset's regex reads bytes (`(?-u)`), so `?` and
# `[..]` take one byte of the UTF-8 text, and a class with a non-ASCII
# char holds that char's bytes as regex-syntax reads `\xNN` escapes.
# `case_insensitive` folds ASCII letters only (`(?-u)(?i)`).

import Base
import ./parse.bend as GParse

# Items
# -----

# the builder options a caller sets: `*`, `?` never match `/` (sep:
# globset's literal_separator); ASCII letters match either case (fold)
type Opts is Data:
  Opts{sep: Bool, fold: Bool}

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
      utf8(GParse.code(c), bytes(t))

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

def rgs(rs: List<&2, GParse.Rg>) -> List<&2, BR>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case GParse.Rg{lo, hi}:
          rg.bytes(GParse.code(lo), GParse.code(hi), rgs(t))

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
def tok(o: Opts, t: GParse.Tok) -> List<&2, List<&2, It>>:
  match o:
    case Opts{sep, +fold}:
      match t:
        case GParse.TLit{c}:
          [lit.go(utf8(GParse.code(c), Nil{}), fold)]
        case GParse.TAny{}:
          [[one_or_star(sep, False{})]]
        case GParse.TZom{}:
          [[one_or_star(sep, True{})]]
        case GParse.TRPre{}:
          [Nil{}, [slash()], [Star{BAny{}}, slash()]]
        case GParse.TRSuf{}:
          [[slash(), Star{BAny{}}]]
        case GParse.TRZom{}:
          [[slash()], [slash(), Star{BAny{}}, slash()]]
        case GParse.TCls{neg, rs}:
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
def seq(+o: Opts, ts: List<&2, GParse.Tok>) -> List<&2, List<&2, It>>:
  match ts:
    case Nil{}:
      [Nil{}]
    case t <> r:
      seq.cross(tok(o, t), seq(o, r))

def alts(+o: Opts, xs: List<&2, List<&2, GParse.Tok>>) -> List<&2, List<&2, It>>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> r:
      List.append(&2, List<&2, It>, seq(o, a), alts(o, r))

# globset's regex of the pattern, as alternatives of byte items
def items(o: Opts, g: GParse.Glob) -> List<&2, List<&2, It>>:
  match g:
    case GParse.Glob{xs, solo}:
      match solo:
        case True{}:
          [[Star{BAny{}}]]
        case False{}:
          alts(o, xs)
