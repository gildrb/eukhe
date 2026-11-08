# autoresearch/dec: the exact decimals of autoresearch's metrics (port of
# oh-my-pi autoresearch, which keeps them as JS numbers): a metric is a
# sign, its decimal digits (most significant first) and a scale (how many
# of them follow the point): Dec{neg, [1, 2, 5], 1} is 12.5. The parser
# (autoresearch/line.bend) answers the canonical form only: no leading
# zero digit, no trailing zero after the point, zero is Dec{False{}, [], 0}.
# Order and printing work on digits, never on one number, so no metric can
# push a Nat past the runtime's bound. laws/autoresearch.bend pins the
# order against the arithmetic of spec/autoresearch/decimal.bend. Pure: no
# IO, no @unsafe.

import Base

# a decimal: sign, digits (0..9, most significant first), scale
type Dec is Data:
  Dec{neg: Bool, ds: List<&2, Nat>, scale: Nat}

def Dec.ds(d: Dec) -> List<&2, Nat>:
  match d:
    case Dec{neg, ds, scale}:
      ds

# Digit lists
# -----------

# n zero digits
def zeros(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0n <> zeros(p)

# xs, then ys
def cat(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case x <> rest:
      x <> cat(rest, ys)

def len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      1n+len(rest)

# some digit is not 0
def nz(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_ne(x, 0n), nz(rest))

# c, unless it is EQ: then d (the order of a pair, first part first)
def then(c: Cmp, d: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      d
    case GT{}:
      GT{}

# the order of two digit lists of one length, first digit first
def lex(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} y <> yr:
      LT{}
    case x <> xr Nil{}:
      GT{}
    case x <> xr y <> yr:
      then(Nat.cmp(x, y), lex(xr, yr))

# Order
# -----

# the order of two magnitudes: both brought to one scale (each takes the
# other's scale of zeros after it), then to one length (zeros before the
# shorter), then compared digit by digit
def mag.pad(+a: List<&2, Nat>, +b: List<&2, Nat>) -> Cmp:
  +la = len(a)
  +lb = len(b)
  lex(cat(zeros(Nat.sub(lb, la)), a), cat(zeros(Nat.sub(la, lb)), b))

def mag(da: List<&2, Nat>, +sa: Nat, db: List<&2, Nat>, +sb: Nat) -> Cmp:
  mag.pad(cat(da, zeros(sb)), cat(db, zeros(sa)))

# a negative against a positive: equal only when both are zero
def cross(any: Bool, c: Cmp) -> Cmp:
  match any:
    case True{}:
      c
    case False{}:
      EQ{}

# the order of two decimals
def Dec.cmp(a: Dec, b: Dec) -> Cmp:
  match a b:
    case Dec{False{}, da, sa} Dec{False{}, db, sb}:
      mag(da, sa, db, sb)
    case Dec{True{}, da, sa} Dec{True{}, db, sb}:
      mag(db, sb, da, sa)
    case Dec{True{}, da, sa} Dec{False{}, db, sb}:
      cross(Bool.or(nz(da), nz(db)), LT{})
    case Dec{False{}, da, sa} Dec{True{}, db, sb}:
      cross(Bool.or(nz(da), nz(db)), GT{})

# Printing
# --------

# the char of a digit
def dchar(d: Nat) -> Char:
  Chr{U32.from_nat(Nat.add(48n, d))}

# the chars of ds, then rest
def put_ds(ds: List<&2, Nat>, rest: String) -> String:
  match ds:
    case Nil{}:
      rest
    case d <> t:
      SCon{dchar(d), put_ds(t, rest)}

def split.on(d: Nat, r: List<&2, Nat> & List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  (a, b) = r
  (d <> a, b)

# the first n digits of ds, then the rest
def split(n: Nat, ds: List<&2, Nat>) -> List<&2, Nat> & List<&2, Nat>:
  match n:
    case 0n:
      (Nil{}, ds)
    case 1n+p:
      match ds:
        case Nil{}:
          (Nil{}, Nil{})
        case d <> t:
          split.on(d, split(p, t))

def show.parts(r: List<&2, Nat> & List<&2, Nat>) -> String:
  (i, f) = r
  put_ds(i, SCon{'.', put_ds(f, "")})

# the magnitude: with fewer digits than the scale, `0.` and the zeros
# the point needs; else the digits with the point scale digits from the
# end; no point at scale 0
def show.mag(more: Bool, ds: List<&2, Nat>, +n: Nat, +scale: Nat) -> String:
  match more:
    case True{}:
      show.parts(split(Nat.sub(n, scale), ds))
    case False{}:
      SCon{'0', SCon{'.', put_ds(zeros(Nat.sub(scale, n)), put_ds(ds, ""))}}

def show.scaled(scale: Nat, +ds: List<&2, Nat>) -> String:
  match scale:
    case 0n:
      put_ds(ds, "")
    case 1n+p:
      +n = len(ds)
      +sc = {1n+p : Nat}
      show.mag(Nat.is_lt(sc, n), ds, n, sc)

def show.sign(neg: Bool, s: String) -> String:
  match neg:
    case True{}:
      SCon{'-', s}
    case False{}:
      s

# the canonical text of a canonical decimal: `0`, `3`, `-12.5`, `0.005`
def show(d: Dec) -> String:
  match d:
    case Dec{neg, ds, scale}:
      match ds:
        case Nil{}:
          "0"
        case h <> t:
          show.sign(neg, show.scaled(scale, h <> t))
