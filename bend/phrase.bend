# phrase: an explicit phrase search, the rule eukhe states instead of a
# regex in a decision (laws/phrase.bend). A phrase is a list of items, each
# one char of a class, one char or none (regex `x?`) or any run of chars
# of a class (regex `x*`), with a condition on the text at each of its
# edges: nothing, a whole word (regex `\b` next to a word char of the
# phrase) or the end of the text (regex `^`, `$`). A word char is an ASCII
# letter, an ASCII digit or `_`. The tables of phrases are data of the
# modules that use them (bend/err_text.bend). Pure: no IO, no @unsafe.

import Base

# Classes, items, edges, phrases
# ------------------------------

# the chars one item takes
type Cls is Data:
  # a char whose code is from lo to hi, both in (a literal c: CIn{c, c})
  CIn{lo: U32, hi: U32}
  # any char but these
  COut{cs: List<&2, Char>}

type It is Data:
  # one char of the class
  One{c: Cls}
  # one char of the class, or none
  Opt{c: Cls}
  # any run of chars of the class, the empty run too
  Star{c: Cls}

# what a phrase asks of the text next to it on one side
type Edge is Data:
  # nothing
  EFree{}
  # a whole word: the text ends there, or its char there is no word char
  EWord{}
  # the text ends there
  EText{}

type Ph is Data:
  Ph{start: Edge, its: List<&2, It>, end: Edge}

def in_range(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

# a word char: an ASCII letter, an ASCII digit or `_`
def is_word(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(in_range(x, 97, 122), Bool.or(in_range(x, 65, 90), Bool.or(in_range(x, 48, 57), U32.is_eq(x, 95))))

# whether x is none of the chars cs
def none_of(cs: List<&2, Char>, +x: Char) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      Bool.and(Bool.not(Char.is_eq(c, x)), none_of(t, x))

# whether the char x is of the class k
def is1(k: Cls, +x: Char) -> Bool:
  match k:
    case CIn{lo, hi}:
      in_range(Char.to_u32(x), lo, hi)
    case COut{cs}:
      none_of(cs, x)

# Search
# ------

# hit, then the rest
def pm.and(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# hit, else the rest
def pm.or(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether the edge e holds for the text s after a phrase
def end_ok(e: Edge, s: String) -> Bool:
  match e:
    case EFree{}:
      True{}
    case EWord{}:
      match s:
        case SNil{}:
          True{}
        case SCon{x, t}:
          Bool.not(is_word(x))
    case EText{}:
      String.is_empty(s)

# whether a phrase with the start edge e may start right after the char x
def step(e: Edge, x: Char) -> Bool:
  match e:
    case EFree{}:
      True{}
    case EWord{}:
      Bool.not(is_word(x))
    case EText{}:
      False{}

# whether some prefix of s matches the items its and the end edge holds for
# the rest of s
def pm(s: String, its: List<&2, It>, +end: Edge) -> Bool:
  match s:
    case SNil{}:
      match its:
        case Nil{}:
          end_ok(end, SNil{})
        case i <> k:
          match i:
            case One{c}:
              False{}
            case Opt{c}:
              pm(SNil{}, k, end)
            case Star{c}:
              pm(SNil{}, k, end)
    case SCon{+x, +t}:
      match its:
        case Nil{}:
          end_ok(end, SCon{x, t})
        case i <> +k:
          match i:
            case One{c}:
              pm.and(is1(c, x), u => pm(t, k, end))
            case Opt{c}:
              pm.or(pm(SCon{x, t}, k, end), u => pm.and(is1(c, x), v => pm(t, k, end)))
            case Star{+c}:
              pm.or(pm(SCon{x, t}, k, end), u => pm.and(is1(c, x), v => pm(t, Star{c} <> k, end)))

# whether some suffix of s, at a place where a phrase may start (may at
# the first place), begins with the phrase
def occ(s: String, +st: Edge, +its: List<&2, It>, +end: Edge, may: Bool) -> Bool:
  match s:
    case SNil{}:
      pm.and(may, u => pm(SNil{}, its, end))
    case SCon{+x, +t}:
      pm.or(pm.and(may, u => pm(SCon{x, t}, its, end)), v => occ(t, st, its, end, step(st, x)))

# whether the phrase ph is found in s
def found(s: String, ph: Ph) -> Bool:
  match ph:
    case Ph{st, its, end}:
      occ(s, st, its, end, True{})

# whether one of the phrases phs is found in s
def any(+s: String, phs: List<&2, Ph>) -> Bool:
  match phs:
    case Nil{}:
      False{}
    case p <> more:
      pm.or(found(s, p), u => any(s, more))

# Tables
# ------

# the chars of s, one item each, before rest
def lit(s: String, rest: List<&2, It>) -> List<&2, It>:
  match s:
    case SNil{}:
      rest
    case SCon{c, t}:
      +x = Char.to_u32(c)
      One{CIn{x, x}} <> lit(t, rest)

# found anywhere
def anywhere(its: List<&2, It>) -> Ph:
  Ph{EFree{}, its, EFree{}}

# found as a whole word on both sides (regex `\b...\b`)
def word(its: List<&2, It>) -> Ph:
  Ph{EWord{}, its, EWord{}}

# found where a word starts (regex `\b...`)
def word_start(its: List<&2, It>) -> Ph:
  Ph{EWord{}, its, EFree{}}
