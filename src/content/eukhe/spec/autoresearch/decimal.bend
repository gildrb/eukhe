# autoresearch (spec): what a decimal metric is worth and how two compare,
# by arithmetic on numbers (the code, bend/autoresearch/dec.bend, works on
# digits): Dec{neg, ds, scale} is ±num(ds) / 10^scale. Its well-formed
# and canonical forms. The laws of area autoresearch
# (laws/autoresearch.bend) speak of these. A spec: the shipped code never
# calls it.

import Base
import ../../bend/autoresearch/dec.bend as D

# the number the digits ds spell (most significant first), after the
# number acc
def num.go(ds: List<&2, Nat>, acc: Nat) -> Nat:
  match ds:
    case Nil{}:
      acc
    case d <> t:
      num.go(t, Nat.add(Nat.mul(acc, 10n), d))

def num(ds: List<&2, Nat>) -> Nat:
  num.go(ds, 0n)

# x · 10^k
def shift(k: Nat, x: Nat) -> Nat:
  match k:
    case 0n:
      x
    case 1n+j:
      shift(j, Nat.mul(x, 10n))

# every item of ds is a decimal digit
def digits_ok(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case d <> t:
      Bool.and(Nat.is_lt(d, 10n), digits_ok(t))

# a decimal is well formed: its digits are digits
def Wf(d: D.Dec) -> Bool:
  match d:
    case D.Dec{neg, ds, scale}:
      digits_ok(ds)

def zero(ds: List<&2, Nat>) -> Bool:
  Nat.is_eq(num(ds), 0n)

# a negative against a non-negative: equal only when both are 0
def order.cross(both_zero: Bool, c: Cmp) -> Cmp:
  match both_zero:
    case True{}:
      EQ{}
    case False{}:
      c

# the order of the values of a and b: a/10^p against b/10^q is a·10^q
# against b·10^p
def order(a: D.Dec, b: D.Dec) -> Cmp:
  match a b:
    case D.Dec{False{}, da, sa} D.Dec{False{}, db, sb}:
      Nat.cmp(shift(sb, num(da)), shift(sa, num(db)))
    case D.Dec{True{}, da, sa} D.Dec{True{}, db, sb}:
      Nat.cmp(shift(sa, num(db)), shift(sb, num(da)))
    case D.Dec{True{}, da, sa} D.Dec{False{}, db, sb}:
      order.cross(Bool.and(zero(da), zero(db)), LT{})
    case D.Dec{False{}, da, sa} D.Dec{True{}, db, sb}:
      order.cross(Bool.and(zero(da), zero(db)), GT{})

# a and b are worth the same
def same(a: D.Dec, b: D.Dec) -> Bool:
  Cmp.is_eq(order(a, b))

# the last digit of ds is not 0
def last_nz(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> t:
      match t:
        case Nil{}:
          Nat.is_ne(d, 0n)
        case e <> u:
          last_nz(e <> u)

def canon.ds(neg: Bool, ds: List<&2, Nat>, +scale: Nat) -> Bool:
  match ds:
    case Nil{}:
      Bool.and(Bool.not(neg), Nat.is_eq(scale, 0n))
    case +h <> +t:
      Bool.and(Nat.is_ne(h, 0n), Bool.and(digits_ok(h <> t), Bool.or(Nat.is_eq(scale, 0n), last_nz(h <> t))))

# the canonical form: digits, no leading 0, no trailing 0 after the point,
# zero is Dec{False{}, [], 0}
def Canon(d: D.Dec) -> Bool:
  match d:
    case D.Dec{neg, ds, scale}:
      canon.ds(neg, ds, scale)

# a is better than b in a direction: lower or higher
def better(lower: Bool, a: D.Dec, b: D.Dec) -> Bool:
  match lower:
    case True{}:
      Cmp.is_lt(order(a, b))
    case False{}:
      Cmp.is_gt(order(a, b))
