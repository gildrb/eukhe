# doc_glob: the rule of glob's ranking and pages
# (crates/eukhe-docs/src/glob.rs). It runs as the compiled core through
# the stepper of bend/ffi_doc_glob.bend, one matched path at a time,
# between the walk's reads.
#
# A matched path has its change time m (ms since the epoch) and its
# display path p (a directory's ends in '/'). Glob ranks the paths newest
# first, then by path (char by char, by code point: Rust's byte order of
# UTF-8; a path before its extensions), and shows each path once: its
# newest copy (copies of one time are one). A page is the K = min(limit,
# 200) ranked paths after the first S (200 with no limit); the
# continuation is S + K when a path follows the page; the skip is past the
# end when paths matched and S is at or past their count. Only the best
# C = S + K + 1 paths can be on the page or tell that more follow, so the
# core keeps those and forgets the others as it goes: its memory is
# bounded by the page, however many paths match; Rust keeps nothing.

import Base

# Pages
# -----

# the most paths a page shows; the page of a glob with no limit
def most() -> Nat:
  200n

# the paths a page shows: the limit, at most most(); most() with no limit
def size(lim: Maybe<&2, Nat>) -> Nat:
  match lim:
    case None{}:
      most()
    case Some{l}:
      Nat.min(l, most())

# the paths the core keeps for the page (s, k): the skip, the page and
# one more (whether more follow)
def keep(+s: Nat, +k: Nat) -> Nat:
  1n+Nat.add(s, k)

# Paths
# -----

# a kept path: changed at m, shown as p, h the hash of p (a quick test
# that two paths differ)
type It is Data:
  It{m: Nat, p: String, h: Nat}

def code(c: Char) -> Nat:
  match c:
    case Chr{x}:
      U32.to_nat(x)

# the hash of the chars of s after those worth acc: their codes, base 31,
# modulo 251 * 251
def hash.go(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      hash.go(t, Nat.mod(Nat.add(Nat.mul(acc, 31n), code(c)), 63001n))

def hash(s: String) -> Nat:
  hash.go(s, 0n)

# the path p changed at m
def it(m: Nat, +p: String) -> It:
  It{m, p, hash(p)}

# Ranking
# -------

# c, when the chars before decided it; else d
def cmp.end(c: Cmp, d: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      d
    case GT{}:
      GT{}

# the order of two paths whose chars before a and b compared c (LT or GT
# is final): char by char, by code point; a path before its extensions
def cmp.go(a: String, b: String, c: Cmp) -> Cmp:
  match a b:
    case SNil{} SNil{}:
      c
    case SNil{} SCon{y, u}:
      cmp.end(c, LT{})
    case SCon{x, t} SNil{}:
      cmp.end(c, GT{})
    case SCon{x, t} SCon{y, u}:
      match c:
        case LT{}:
          LT{}
        case EQ{}:
          cmp.go(t, u, Nat.cmp(code(x), code(y)))
        case GT{}:
          GT{}

# how a path x stands to a kept path y
type Rel is Data:
  Ahead{}    # x ranks before y
  Twin{}     # y is x's path and ranks at least as high: x goes
  Behind{}   # x ranks after y and is another path

# same time: the paths decide
def rel.path(c: Cmp) -> Rel:
  match c:
    case LT{}:
      Ahead{}
    case EQ{}:
      Twin{}
    case GT{}:
      Behind{}

# x is older: y is x's path or another
def rel.same(c: Cmp) -> Rel:
  match c:
    case LT{}:
      Behind{}
    case EQ{}:
      Twin{}
    case GT{}:
      Behind{}

# x is older; e: the hashes are equal (else the paths differ)
def rel.older(e: Bool, +xp: String, +yp: String) -> Rel:
  match e:
    case True{}:
      rel.same(cmp.go(xp, yp, EQ{}))
    case False{}:
      Behind{}

def rel.time(c: Cmp, +xp: String, +xh: Nat, +yp: String, +yh: Nat) -> Rel:
  match c:
    case LT{}:
      rel.older(Nat.is_eq(xh, yh), xp, yp)
    case EQ{}:
      rel.path(cmp.go(xp, yp, EQ{}))
    case GT{}:
      Ahead{}

def rel(+x: It, +y: It) -> Rel:
  match x y:
    case It{+xm, +xp, +xh} It{+ym, +yp, +yh}:
      rel.time(Nat.cmp(xm, ym), xp, xh, yp, yh)

# e: the hashes are equal (else the paths differ)
def named.h(e: Bool, +xp: String, +yp: String) -> Bool:
  match e:
    case True{}:
      Cmp.is_eq(cmp.go(xp, yp, EQ{}))
    case False{}:
      False{}

# y is x's path
def named(+x: It, +y: It) -> Bool:
  match x y:
    case It{xm, +xp, +xh} It{ym, +yp, +yh}:
      named.h(Nat.is_eq(xh, yh), xp, yp)

# y <> t without its first path of x's path (b: y is)
def rm.go(t: List<&2, It>, +x: It, y: It, b: Bool) -> List<&2, It>:
  match t:
    case Nil{}:
      match b:
        case True{}:
          Nil{}
        case False{}:
          [y]
    case +z <> u:
      match b:
        case True{}:
          z <> u
        case False{}:
          y <> rm.go(u, x, z, named(x, z))

# x put into the ranked paths y <> t (r: how x stands to y): before the
# first path it ranks before, where the older copy of its path (if any)
# leaves; or dropped when a copy of its path ranks at least as high
def ins.go(t: List<&2, It>, +x: It, +y: It, r: Rel) -> List<&2, It>:
  match t:
    case Nil{}:
      match r:
        case Ahead{}:
          x <> rm.go(Nil{}, x, y, named(x, y))
        case Twin{}:
          [y]
        case Behind{}:
          [y, x]
    case +z <> u:
      match r:
        case Ahead{}:
          x <> rm.go(z <> u, x, y, named(x, y))
        case Twin{}:
          y <> z <> u
        case Behind{}:
          y <> ins.go(u, x, z, rel(x, z))

# x put into the ranked paths xs
def ins(+x: It, xs: List<&2, It>) -> List<&2, It>:
  match xs:
    case Nil{}:
      [x]
    case +y <> t:
      ins.go(t, x, y, rel(x, y))

# Keeping
# -------

# what the core keeps of a ranked list: its first paths, how many and
# the oldest time among them (0 for none)
type Fin is Data:
  Fin{kept: List<&2, It>, len: Nat, low: Nat}

# the oldest time of y's and the n kept paths after it (oldest lo)
def low(+m: Nat, n: Nat, +lo: Nat) -> Nat:
  match n:
    case 0n:
      m
    case 1n+j:
      Nat.min(m, lo)

def fin.cons(y: It, f: Fin) -> Fin:
  match y f:
    case It{+m, p, h} Fin{k, +n, lo}:
      Fin{It{m, p, h} <> k, 1n+n, low(m, n, lo)}

# the first c paths of xs are kept
def fin(xs: List<&2, It>, c: Nat) -> Fin:
  match xs c:
    case Nil{} c:
      Fin{Nil{}, 0n, 0n}
    case y <> t 0n:
      Fin{Nil{}, 0n, 0n}
    case y <> t 1n+d:
      fin.cons(y, fin(t, d))

# Page
# ----

# the first k paths of xs
def first(xs: List<&2, It>, k: Nat) -> List<&2, It>:
  match xs k:
    case Nil{} k:
      Nil{}
    case y <> t 0n:
      Nil{}
    case y <> t 1n+j:
      y <> first(t, j)

# xs after its first s paths
def after(xs: List<&2, It>, s: Nat) -> List<&2, It>:
  match xs s:
    case Nil{} s:
      Nil{}
    case y <> t 0n:
      y <> t
    case y <> t 1n+j:
      after(t, j)

# the page of the kept paths xs: k of them after the first s
def page(xs: List<&2, It>, +s: Nat, k: Nat) -> List<&2, It>:
  first(after(xs, s), k)

def when(b: Bool, +v: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      None{}

# the continuation of the page (s, k) when len paths are kept (at most
# s + k + 1): s + k when a path follows the page
def next(+s: Nat, k: Nat, +len: Nat) -> Maybe<&2, Nat>:
  match k:
    case 0n:
      None{}
    case 1n+j:
      +c = Nat.add(s, 1n+j)
      when(Nat.is_lt(c, len), c)

# the count of the len kept paths when the skip s is at or past it and
# paths matched (len is their count then: the core keeps s + k + 1)
def past(+s: Nat, +len: Nat) -> Maybe<&2, Nat>:
  when(Bool.and(Nat.is_le(len, s), Nat.is_lt(0n, len)), len)
