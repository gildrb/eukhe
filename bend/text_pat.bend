# text_pat: the text patterns the eukhe-ai error rules look for (Rust:
# the `regex` patterns of eukhe-ai utils/overflow.rs and
# utils/stream_failure.rs). A pattern is a list of alternatives; each
# alternative is a list of items, one char of a class or any run of chars
# of a class (the regex `*`). The callers spell each regex as its
# alternatives (an optional group or an alternation becomes two
# alternatives; `x+` becomes `x x*`; an optional or repeated tail is
# dropped, since a search that finds the head finds the whole). Case:
# `fold` folds a text for a case-insensitive search of a lowercase ASCII
# pattern (regex `(?i)`), `lower` lowers it as Rust's `to_lowercase`
# does for every char a lowercase ASCII pattern can tell apart. Pure: no
# IO, no @unsafe; laws/text_pat.bend states its laws.

import Base

# Classes and items
# -----------------

# the chars one item matches
type Cls is Data:
  # exactly this char
  CLit{c: Char}
  # any char but a line feed (regex `.`)
  CAny{}
  # an ASCII digit (regex `[0-9]`)
  CDig{}
  # an ASCII digit or a comma (regex `[0-9,]`)
  CDigC{}
  # a Unicode White_Space char (regex `\s`)
  CSp{}

type It is Data:
  # one char of the class
  One{c: Cls}
  # any run of chars of the class, the empty run too
  Star{c: Cls}

# a pattern: its alternatives, found anywhere or only at the start
type Pat is Data:
  Pat{anchored: Bool, alts: List<&2, List<&2, It>>}

# Unicode White_Space: U+0009..U+000D, U+0020, U+0085, U+00A0, U+1680,
# U+2000..U+200A, U+2028, U+2029, U+202F, U+205F, U+3000
def is_ws(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

def is_dig(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and(U32.is_le(48, x), U32.is_le(x, 57))

# whether the char x is of the class k
def is1(k: Cls, +x: Char) -> Bool:
  match k:
    case CLit{c}:
      Char.is_eq(c, x)
    case CAny{}:
      Bool.not(Char.is_eq(x, '\n'))
    case CDig{}:
      is_dig(x)
    case CDigC{}:
      Bool.or(is_dig(x), Char.is_eq(x, ','))
    case CSp{}:
      is_ws(x)

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

# whether some prefix of s matches the items its
def pm(s: String, its: List<&2, It>) -> Bool:
  match s:
    case SNil{}:
      match its:
        case Nil{}:
          True{}
        case i <> k:
          match i:
            case One{c}:
              False{}
            case Star{c}:
              pm(SNil{}, k)
    case SCon{+x, +t}:
      match its:
        case Nil{}:
          True{}
        case i <> +k:
          match i:
            case One{c}:
              pm.and(is1(c, x), u => pm(t, k))
            case Star{+c}:
              pm.or(pm(SCon{x, t}, k), u => pm.and(is1(c, x), v => pm(t, Star{c} <> k)))

# whether some part of s matches the items its
def occ(s: String, +its: List<&2, It>) -> Bool:
  match s:
    case SNil{}:
      pm(SNil{}, its)
    case SCon{+x, +t}:
      pm.or(pm(SCon{x, t}, its), u => occ(t, its))

# whether the alternative its is found in s: at its start, or anywhere
def found(anchored: Bool, +s: String, +its: List<&2, It>) -> Bool:
  match anchored:
    case True{}:
      pm(s, its)
    case False{}:
      occ(s, its)

# whether one of the alternatives is found in s
def hit.go(+anchored: Bool, +s: String, alts: List<&2, List<&2, It>>) -> Bool:
  match alts:
    case Nil{}:
      False{}
    case its <> +more:
      pm.or(found(anchored, s, its), u => hit.go(anchored, s, more))

# whether the pattern p is found in s
def hit(+s: String, p: Pat) -> Bool:
  match p:
    case Pat{a, alts}:
      hit.go(a, s, alts)

# whether one of the patterns ps is found in s
def any(+s: String, ps: List<&2, Pat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> more:
      pm.or(hit(s, p), u => any(s, more))

# Case
# ----

def fold.at(+x: U32, upper: Bool, kelvin: Bool, longs: Bool) -> Char:
  match upper kelvin longs:
    case True{} _ _:
      Chr{U32.add(x, 32)}
    case False{} True{} _:
      'k'
    case False{} False{} True{}:
      's'
    case False{} False{} False{}:
      Chr{x}

# the char as a case-insensitive search of a lowercase ASCII pattern sees
# it (Unicode simple case folding, as far as it reaches ASCII): A-Z as
# a-z, the Kelvin sign U+212A as k, the long s U+017F as s
def fold(c: Char) -> Char:
  match c:
    case Chr{+x}:
      fold.at(x, Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), U32.is_eq(x, 8490), U32.is_eq(x, 383))

def fold_str(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{fold(c), fold_str(t)}

def lower.at(+x: U32, upper: Bool, kelvin: Bool, idot: Bool, rest: String) -> String:
  match upper kelvin idot:
    case True{} _ _:
      SCon{Chr{U32.add(x, 32)}, rest}
    case False{} True{} _:
      SCon{'k', rest}
    case False{} False{} True{}:
      SCon{'i', SCon{Chr{775}, rest}}
    case False{} False{} False{}:
      SCon{Chr{x}, rest}

# the text as Rust's `to_lowercase` writes it, for every char a lowercase
# ASCII pattern tells apart: A-Z as a-z, the Kelvin sign U+212A as k, the
# capital I with dot U+0130 as i and U+0307 (two chars); every other
# char stays one char that is no ASCII letter
def lower(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          lower.at(x, Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), U32.is_eq(x, 8490), U32.is_eq(x, 304), lower(t))
