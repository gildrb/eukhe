# autoresearch/stats: the confidence a snapshot shows (port of oh-my-pi
# autoresearch state.ts `computeConfidence`): how far the segment's best
# kept metric is from its baseline, in units of the median absolute
# deviation (MAD) of the segment's logged metrics that are not flagged:
#
#   confidence = |best - baseline| / MAD,  MAD = median |v - median(vs)|
#
# answered in tenths, rounded down, at most 999999999; none with fewer
# than 3 metrics, a MAD of 0, no baseline, or best equal to baseline.
# Exact: the metrics are brought to one scale and shifted by the
# smallest (the deviations do not change), then everything is a natural
# number of decimal digits (least significant first), doubled where a
# median would halve: med2 = 2·median, dev2 = |2·v - med2|, mad4 = 4·MAD,
# so tenths = floor(40·|best - baseline| / mad4). Pure: no IO, no
# @unsafe.

import Base
import ./dec.bend as D
import ./line.bend as L
import ./state.bend as S

# Naturals as digits, least significant first
# --------------------------------------------

# the order of a and b, given the order acc of their lower digits
def big.cmp(a: List<&2, Nat>, b: List<&2, Nat>, acc: Cmp) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      acc
    case Nil{} y <> yr:
      big.cmp(Nil{}, yr, D.then(Nat.cmp(0n, y), acc))
    case x <> xr Nil{}:
      big.cmp(xr, Nil{}, D.then(Nat.cmp(x, 0n), acc))
    case x <> xr y <> yr:
      big.cmp(xr, yr, D.then(Nat.cmp(x, y), acc))

def big.add.last(c: Nat) -> List<&2, Nat>:
  match c:
    case 0n:
      Nil{}
    case 1n+p:
      [1n+p]

def big.add.at(+s: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  Nat.mod(s, 10n) <> r

# a + b + carry
def big.add(a: List<&2, Nat>, b: List<&2, Nat>, +carry: Nat) -> List<&2, Nat>:
  match a b:
    case Nil{} Nil{}:
      big.add.last(carry)
    case Nil{} y <> yr:
      +s = Nat.add(y, carry)
      big.add.at(s, big.add(Nil{}, yr, Nat.div(s, 10n)))
    case x <> xr Nil{}:
      +s = Nat.add(x, carry)
      big.add.at(s, big.add(xr, Nil{}, Nat.div(s, 10n)))
    case x <> xr y <> yr:
      +s = Nat.add(x, Nat.add(y, carry))
      big.add.at(s, big.add(xr, yr, Nat.div(s, 10n)))

def big.sub.at(low: Bool, +x: Nat, +k: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match low:
    case True{}:
      Nat.sub(Nat.add(10n, x), k) <> r
    case False{}:
      Nat.sub(x, k) <> r

# a - b - borrow, for a >= b + borrow
def big.sub(a: List<&2, Nat>, b: List<&2, Nat>, +borrow: Nat) -> List<&2, Nat>:
  match a b:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} y <> yr:
      Nil{}
    case +x <> xr Nil{}:
      +low = Nat.is_lt(x, borrow)
      big.sub.at(low, x, borrow, big.sub(xr, Nil{}, S.one(low)))
    case +x <> xr y <> yr:
      +k = Nat.add(y, borrow)
      +low = Nat.is_lt(x, k)
      big.sub.at(low, x, k, big.sub(xr, yr, S.one(low)))

def big.diff.at(c: Cmp, a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case LT{}:
      big.sub(b, a, 0n)
    case EQ{}:
      big.sub(a, b, 0n)
    case GT{}:
      big.sub(a, b, 0n)

# |a - b|
def big.diff(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  big.diff.at(big.cmp(a, b, EQ{}), a, b)

def big.double(+a: List<&2, Nat>) -> List<&2, Nat>:
  big.add(a, a, 0n)

def big.zero(a: List<&2, Nat>) -> Bool:
  Bool.not(D.nz(a))

# the decimal digits of n, least significant first (fuel f >= n)
def big.of.go(f: Nat, n: Nat) -> List<&2, Nat>:
  match f:
    case 0n:
      Nil{}
    case 1n+g:
      match n:
        case 0n:
          Nil{}
        case 1n+p:
          +m = {1n+p : Nat}
          Nat.mod(m, 10n) <> big.of.go(g, Nat.div(m, 10n))

# the digits of a small n (a count)
def big.of(+n: Nat) -> List<&2, Nat>:
  big.of.go(n, n)

# Division
# --------

def div.digit.at(less: Bool, +r: List<&2, Nat>, +q: Nat, more: Nat & List<&2, Nat>) -> Nat & List<&2, Nat>:
  match less:
    case True{}:
      (q, r)
    case False{}:
      more

# r = rem; take b off it while it lasts, at most f times: the count and
# what is left
def div.digit(f: Nat, +r: List<&2, Nat>, +b: List<&2, Nat>, +q: Nat) -> Nat & List<&2, Nat>:
  match f:
    case 0n:
      (q, r)
    case 1n+g:
      div.digit.at(Cmp.is_lt(big.cmp(r, b, EQ{})), r, q, div.digit(g, big.sub(r, b, 0n), b, 1n+q))

# long division: the digits ds of the dividend still to take, most
# significant first; the last quotient digit and the remainder; the
# quotient's digits before it, last first
def div.go(ds: List<&2, Nat>, qr: Nat & List<&2, Nat>, +b: List<&2, Nat>, qs: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      (q, r) = qr
      q <> qs
    case d <> t:
      (q, r) = qr
      div.go(t, div.digit(9n, d <> r, b, 0n), b, q <> qs)

def rev(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev(t, x <> acc)

# the value of digits, least significant first
def big.val(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(x, Nat.mul(big.val(t), 10n))

def cap() -> Nat:
  999999999n

def div.fit(fit: Bool, +q: List<&2, Nat>) -> Nat:
  match fit:
    case True{}:
      big.val(q)
    case False{}:
      cap()

# floor(a / b), at most cap(), for b > 0
def div(a: List<&2, Nat>, +b: List<&2, Nat>) -> Nat:
  +q = L.strip(div.go(rev(a, Nil{}), (0n, Nil{}), b, Nil{}))
  div.fit(Nat.is_le(D.len(q), 9n), q)

# The metrics
# -----------

def vals.at(ok: Bool, m: Maybe<&2, D.Dec>, r: List<&2, D.Dec>) -> List<&2, D.Dec>:
  match ok:
    case False{}:
      r
    case True{}:
      match m:
        case None{}:
          r
        case Some{x}:
          x <> r

# the metrics of the segment's logged runs that are not flagged
def vals(rs: List<&2, S.Row>, +seg: Nat) -> List<&2, D.Dec>:
  match rs:
    case Nil{}:
      Nil{}
    case S.Row{id, sg, st, m, ms, ps, fn, fl, desc} <> t:
      vals.at(Bool.and(Nat.is_eq(sg, seg), Bool.and(S.has(st), Bool.not(fl))), m, vals(t, seg))

def scale(d: D.Dec) -> Nat:
  match d:
    case D.Dec{neg, ds, sc}:
      sc

# the largest scale of vs
def top_scale(vs: List<&2, D.Dec>) -> Nat:
  match vs:
    case Nil{}:
      0n
    case v <> t:
      Nat.max(scale(v), top_scale(t))

def low.at(less: Bool, +v: D.Dec, +m: D.Dec) -> D.Dec:
  match less:
    case True{}:
      v
    case False{}:
      m

# the smallest of v and vs
def low(+v: D.Dec, vs: List<&2, D.Dec>) -> D.Dec:
  match vs:
    case Nil{}:
      v
    case +w <> t:
      +m = low(v, t)
      low.at(Cmp.is_lt(D.Dec.cmp(w, m)), w, m)

# the magnitude of d at scale sc, least significant digit first
def mag(d: D.Dec, +sc: Nat) -> List<&2, Nat>:
  match d:
    case D.Dec{neg, ds, s}:
      rev(D.cat(ds, D.zeros(Nat.sub(sc, s))), Nil{})

def neg(d: D.Dec) -> Bool:
  match d:
    case D.Dec{n, ds, s}:
      n

def diff.signs(same: Bool, +a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  match same:
    case True{}:
      big.diff(a, b)
    case False{}:
      big.add(a, b, 0n)

# |a - b| at scale sc
def diff(+a: D.Dec, +b: D.Dec, +sc: Nat) -> List<&2, Nat>:
  diff.signs(Bool.not(Bool.xor(neg(a), neg(b))), mag(a, sc), mag(b, sc))

# Median
# ------

def ins.at(le: Bool, +x: List<&2, Nat>, +y: List<&2, Nat>, t: List<&2, List<&2, Nat>>, r: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match le:
    case True{}:
      x <> (y <> t)
    case False{}:
      y <> r

# x into the ascending xs
def ins(+x: List<&2, Nat>, xs: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      [x]
    case +y <> +t:
      ins.at(Cmp.is_le(big.cmp(x, y, EQ{})), x, y, t, ins(x, t))

# xs, ascending
def sort(xs: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      ins(x, sort(t))

def at(xs: List<&2, List<&2, Nat>>, i: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      match i:
        case 0n:
          x
        case 1n+j:
          at(t, j)

def med2.at(odd: Bool, +xs: List<&2, List<&2, Nat>>, +h: Nat) -> List<&2, Nat>:
  match odd:
    case True{}:
      big.double(at(xs, h))
    case False{}:
      big.add(at(xs, Nat.sub(h, 1n)), at(xs, h), 0n)

# twice the median of the ascending xs (n of them)
def med2(+xs: List<&2, List<&2, Nat>>, +n: Nat) -> List<&2, Nat>:
  med2.at(Nat.is_eq(Nat.mod(n, 2n), 1n), xs, Nat.div(n, 2n))

def devs(xs: List<&2, List<&2, Nat>>, +m: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      big.diff(big.double(x), m) <> devs(t, m)

def shifted(vs: List<&2, D.Dec>, +lo: D.Dec, +sc: Nat) -> List<&2, List<&2, Nat>>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> t:
      diff(v, lo, sc) <> shifted(t, lo, sc)

# Confidence
# ----------

def conf.mad(zero: Bool, +d: List<&2, Nat>, +mad4: List<&2, Nat>) -> Maybe<&2, Nat>:
  match zero:
    case True{}:
      None{}
    case False{}:
      Some{div(D.cat([0n], big.double(big.double(d))), mad4)}

def conf.go(+vs: List<&2, D.Dec>, +n: Nat, +base: D.Dec, +best: D.Dec) -> Maybe<&2, Nat>:
  +sc = top_scale(vs)
  +xs = sort(shifted(vs, low(base, vs), sc))
  +ys = sort(devs(xs, med2(xs, n)))
  +mad4 = med2(ys, n)
  conf.mad(big.zero(mad4), diff(best, base, sc), mad4)

def conf.same(c: Cmp, +vs: List<&2, D.Dec>, +n: Nat, +base: D.Dec, +best: D.Dec) -> Maybe<&2, Nat>:
  match c:
    case EQ{}:
      None{}
    case LT{}:
      conf.go(vs, n, base, best)
    case GT{}:
      conf.go(vs, n, base, best)

def conf.pair(b: Maybe<&2, D.Dec>, x: Maybe<&2, D.Dec>, vs: List<&2, D.Dec>, +n: Nat) -> Maybe<&2, Nat>:
  match b x:
    case Some{+base} Some{+best}:
      conf.same(D.Dec.cmp(best, base), vs, n, base, best)
    case Some{base} None{}:
      None{}
    case None{} x:
      None{}

def conf.count(enough: Bool, b: Maybe<&2, D.Dec>, x: Maybe<&2, D.Dec>, vs: List<&2, D.Dec>, +n: Nat) -> Maybe<&2, Nat>:
  match enough:
    case True{}:
      conf.pair(b, x, vs, n)
    case False{}:
      None{}

def dlen(vs: List<&2, D.Dec>) -> Nat:
  match vs:
    case Nil{}:
      0n
    case v <> t:
      1n+dlen(t)

# the segment's confidence, in tenths
def St.confidence(s: S.St) -> Maybe<&2, Nat>:
  match s:
    case S.St{c, +seg, mode, +runs, pend}:
      +vs = vals(runs, seg)
      +n = dlen(vs)
      conf.count(Nat.is_le(3n, n), S.first(runs, seg), S.last(runs, seg), vs, n)
