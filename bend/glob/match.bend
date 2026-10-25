# glob/match: the items run over the UTF-8 bytes of a text (step 3 of
# bend/glob/): the whole text, one alternative at a time, by a table that
# holds, for each suffix of the text, which suffixes of the items match
# it (time: bytes x items per alternative; no backtracking).

import Base
import ./parse.bend as GParse
import ./items.bend as GItems

# Matching
# --------

def in_rs(rs: List<&2, GItems.BR>, +x: U32) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case GItems.BR{lo, hi}:
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

def in_set(+rs: List<&2, GItems.BR>, +x: U32, fold: Bool) -> Bool:
  match fold:
    case True{}:
      Bool.or(in_rs(rs, x), in_rs(rs, swap(x)))
    case False{}:
      in_rs(rs, x)

# whether the byte x is of the class k
def bc(k: GItems.BC, +x: U32) -> Bool:
  match k:
    case GItems.BAny{}:
      True{}
    case GItems.BNotSl{}:
      Bool.not(U32.is_eq(x, 47))
    case GItems.BSet{neg, fold, rs}:
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
def nul(its: List<&2, GItems.It>) -> List<&2, Bool>:
  match its:
    case Nil{}:
      [True{}]
    case i <> k:
      match i:
        case GItems.One{c}:
          False{} <> nul(k)
        case GItems.Star{c}:
          +r = nul(k)
          hd(r) <> r

def row.cons(i: GItems.It, +x: U32, p: Bool, +pr: List<&2, Bool>, +rest: List<&2, Bool>) -> List<&2, Bool>:
  match i:
    case GItems.One{c}:
      Bool.and(bc(c, x), hd(pr)) <> rest
    case GItems.Star{c}:
      Bool.or(hd(rest), Bool.and(bc(c, x), p)) <> rest

# the row of the text x <> t from prev, the row of t: the items i <> k
# match x <> t when i takes x and k matches t (One), or k matches x <> t
# or i takes x and i <> k matches t (Star)
def row(its: List<&2, GItems.It>, +x: U32, prev: List<&2, Bool>) -> List<&2, Bool>:
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
def rows(bs: List<&2, U32>, +its: List<&2, GItems.It>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      nul(its)
    case x <> t:
      row(its, x, rows(t, its))

# whether the items match the whole byte text
def full(+bs: List<&2, U32>, its: List<&2, GItems.It>) -> Bool:
  hd(rows(bs, its))

# hit, else the rest (the rest runs only on a miss)
def or_else(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether one of the alternatives matches the whole byte text
def any_full(+bs: List<&2, U32>, xs: List<&2, List<&2, GItems.It>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case a <> r:
      or_else(full(bs, a), u => any_full(bs, r))

# whether the parsed pattern matches the whole text
def matches(o: GItems.Opts, g: GParse.Glob, s: String) -> Bool:
  any_full(GItems.bytes(s), GItems.items(o, g))
