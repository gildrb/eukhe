# autoresearch (spec): the confidence of a segment, by arithmetic on
# numbers (oh-my-pi state.ts `computeConfidence`, `sortedMedian`): how
# far the best is from the baseline in units of the median absolute
# deviation (MAD) of the segment's metrics,
#
#   confidence = |best - baseline| / MAD,  MAD = median |v - median(vs)|
#
# in tenths, rounded down, at most cap() = 999999999; none with fewer
# than 3 metrics, no baseline or best, best worth the baseline, or a MAD
# of 0. Every metric is an exact integer at the metrics' largest scale
# (./decimal.bend); medians are kept doubled (2·median is an integer) so
# nothing is rounded: tenths = floor(40·|best - baseline| / (4·MAD)). A
# spec: the shipped code never calls it.

import Base
import ../../bend/autoresearch/dec.bend as D
import ./decimal.bend as Dec

# a signed integer: negative, magnitude
type Z is Data:
  Z{neg: Bool, mag: Nat}

def scale(d: D.Dec) -> Nat:
  match d:
    case D.Dec{neg, ds, sc}:
      sc

# the largest scale of vs
def top(vs: List<&2, D.Dec>) -> Nat:
  match vs:
    case Nil{}:
      0n
    case v <> t:
      Nat.max(scale(v), top(t))

# the value of d as an integer at scale sc (sc at least d's scale)
def z(d: D.Dec, +sc: Nat) -> Z:
  match d:
    case D.Dec{neg, ds, s}:
      +m = Dec.num(ds)
      Z{Bool.and(neg, Nat.is_ne(m, 0n)), Dec.shift(Nat.sub(sc, s), m)}

# a <= b
def z_le(a: Z, b: Z) -> Bool:
  match a b:
    case Z{False{}, x} Z{False{}, y}:
      Nat.is_le(x, y)
    case Z{True{}, x} Z{True{}, y}:
      Nat.is_le(y, x)
    case Z{True{}, x} Z{False{}, y}:
      True{}
    case Z{False{}, x} Z{True{}, y}:
      Bool.and(Nat.is_eq(x, 0n), Nat.is_eq(y, 0n))

def z_dist.of(apart: Bool, +x: Nat, +y: Nat) -> Nat:
  match apart:
    case True{}:
      Nat.add(x, y)
    case False{}:
      Nat.add(Nat.sub(x, y), Nat.sub(y, x))

# |a - b|
def z_dist(a: Z, b: Z) -> Nat:
  match a b:
    case Z{na, +x} Z{nb, +y}:
      z_dist.of(Bool.xor(na, nb), x, y)

def z_add.of(na: Bool, nb: Bool, +x: Nat, +y: Nat) -> Z:
  match na nb:
    case False{} False{}:
      Z{False{}, Nat.add(x, y)}
    case True{} True{}:
      Z{True{}, Nat.add(x, y)}
    case False{} True{}:
      Z{Nat.is_lt(x, y), Nat.add(Nat.sub(x, y), Nat.sub(y, x))}
    case True{} False{}:
      Z{Nat.is_lt(y, x), Nat.add(Nat.sub(x, y), Nat.sub(y, x))}

# a + b
def z_add(a: Z, b: Z) -> Z:
  match a b:
    case Z{na, +x} Z{nb, +y}:
      z_add.of(na, nb, x, y)

def zins.at(le: Bool, +x: Z, +y: Z, t: List<&2, Z>, r: List<&2, Z>) -> List<&2, Z>:
  match le:
    case True{}:
      x <> (y <> t)
    case False{}:
      y <> r

# x into the ascending zs
def zins(+x: Z, zs: List<&2, Z>) -> List<&2, Z>:
  match zs:
    case Nil{}:
      [x]
    case +y <> +t:
      zins.at(z_le(x, y), x, y, t, zins(x, t))

def zsort(zs: List<&2, Z>) -> List<&2, Z>:
  match zs:
    case Nil{}:
      Nil{}
    case x <> t:
      zins(x, zsort(t))

def nins.at(le: Bool, +x: Nat, +y: Nat, t: List<&2, Nat>, r: List<&2, Nat>) -> List<&2, Nat>:
  match le:
    case True{}:
      x <> (y <> t)
    case False{}:
      y <> r

# x into the ascending ns
def nins(+x: Nat, ns: List<&2, Nat>) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      [x]
    case +y <> +t:
      nins.at(Nat.is_le(x, y), x, y, t, nins(x, t))

def nsort(ns: List<&2, Nat>) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case x <> t:
      nins(x, nsort(t))

def zat(zs: List<&2, Z>, i: Nat) -> Z:
  match zs:
    case Nil{}:
      Z{False{}, 0n}
    case x <> t:
      match i:
        case 0n:
          x
        case 1n+j:
          zat(t, j)

def nat_at(ns: List<&2, Nat>, i: Nat) -> Nat:
  match ns:
    case Nil{}:
      0n
    case x <> t:
      match i:
        case 0n:
          x
        case 1n+j:
          nat_at(t, j)

def zmed2.at(odd: Bool, +zs: List<&2, Z>, +h: Nat) -> Z:
  match odd:
    case True{}:
      z_add(zat(zs, h), zat(zs, h))
    case False{}:
      z_add(zat(zs, Nat.sub(h, 1n)), zat(zs, h))

# twice the median of the ascending zs (n of them): the middle one twice,
# or the two middle ones added
def zmed2(+zs: List<&2, Z>, +n: Nat) -> Z:
  zmed2.at(Nat.is_eq(Nat.mod(n, 2n), 1n), zs, Nat.div(n, 2n))

def nmed2.at(odd: Bool, +ns: List<&2, Nat>, +h: Nat) -> Nat:
  match odd:
    case True{}:
      Nat.add(nat_at(ns, h), nat_at(ns, h))
    case False{}:
      Nat.add(nat_at(ns, Nat.sub(h, 1n)), nat_at(ns, h))

def nmed2(+ns: List<&2, Nat>, +n: Nat) -> Nat:
  nmed2.at(Nat.is_eq(Nat.mod(n, 2n), 1n), ns, Nat.div(n, 2n))

def zs_of(vs: List<&2, D.Dec>, +sc: Nat) -> List<&2, Z>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> t:
      z(v, sc) <> zs_of(t, sc)

# 2·|v - median| for each v: |2v - 2·median|
def devs2(zs: List<&2, Z>, +m2: Z) -> List<&2, Nat>:
  match zs:
    case Nil{}:
      Nil{}
    case +x <> t:
      z_dist(z_add(x, x), m2) <> devs2(t, m2)

def cap() -> Nat:
  999999999n

# n with its last k decimal digits dropped: n / 10^k
def shed(k: Nat, n: Nat) -> Nat:
  match k:
    case 0n:
      n
    case 1n+j:
      shed(j, Nat.div(n, 10n))

def capped.at(small: Bool, +x: Nat) -> Nat:
  match small:
    case True{}:
      x
    case False{}:
      cap()

# x, at most cap(): x when it has at most 9 decimal digits (x / 10^9 is
# 0, so x <= cap()), else cap() (min(x, cap()) by digit count, so the
# checker never builds 10^9)
def capped(+x: Nat) -> Nat:
  capped.at(Nat.is_eq(shed(9n, x), 0n), x)

def len(vs: List<&2, D.Dec>) -> Nat:
  match vs:
    case Nil{}:
      0n
    case v <> t:
      1n+len(t)

# 4·MAD of the metrics vs, at scale sc
def mad4(+vs: List<&2, D.Dec>, +sc: Nat) -> Nat:
  +zs = zsort(zs_of(vs, sc))
  nmed2(nsort(devs2(zs, zmed2(zs, len(vs)))), len(vs))

def confidence.mad(zero: Bool, +m4: Nat, +d: Nat) -> Maybe<&2, Nat>:
  match zero:
    case True{}:
      None{}
    case False{}:
      Some{capped(Nat.div(Nat.mul(40n, d), m4))}

def confidence.of(+vs: List<&2, D.Dec>, +base: D.Dec, +best: D.Dec) -> Maybe<&2, Nat>:
  +sc = top(vs)
  +m4 = mad4(vs, sc)
  confidence.mad(Nat.is_eq(m4, 0n), m4, z_dist(z(best, sc), z(base, sc)))

def confidence.same(eq: Bool, +vs: List<&2, D.Dec>, +b: D.Dec, +x: D.Dec) -> Maybe<&2, Nat>:
  match eq:
    case True{}:
      None{}
    case False{}:
      confidence.of(vs, b, x)

def confidence.pair(+vs: List<&2, D.Dec>, base: Maybe<&2, D.Dec>, best: Maybe<&2, D.Dec>) -> Maybe<&2, Nat>:
  match base best:
    case Some{+b} Some{+x}:
      confidence.same(Dec.same(x, b), vs, b, x)
    case Some{b} None{}:
      None{}
    case None{} x:
      None{}

def confidence.count(enough: Bool, +vs: List<&2, D.Dec>, base: Maybe<&2, D.Dec>, best: Maybe<&2, D.Dec>) -> Maybe<&2, Nat>:
  match enough:
    case False{}:
      None{}
    case True{}:
      confidence.pair(vs, base, best)

# the confidence, in tenths, of the metrics vs (the segment's logged runs
# that are not flagged), given the baseline and the best
def confidence(+vs: List<&2, D.Dec>, base: Maybe<&2, D.Dec>, best: Maybe<&2, D.Dec>) -> Maybe<&2, Nat>:
  confidence.count(Nat.is_le(3n, len(vs)), vs, base, best)
