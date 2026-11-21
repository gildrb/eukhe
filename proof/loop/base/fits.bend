# eukhe: area loop, lemmas of what fits the wire. The digit count of the
# wire (LawsBase.wire_digits) is monotone: a Nat no larger has no more
# digits, so a count one fewer fits when the count fits. The code's test
# of the wire (Lp.fits) is the wire's (LawsBase.wire_fits), so the
# deadline of a span (Lp.until.cut) fits, and is the law's (Loop.lp_cut).

import Base
import ../../../bend/loop.bend as Lp
import ../../../laws/base.bend as LawsBase
import ../../../laws/loop/model.bend as Loop
import ../../wire/base.bend as LAWire
import ../../wire/wire_u32_round_trip.bend as PWireU32RoundTrip


# Order
# -----

def lf.le_zero(+n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def lf.le_succ(+n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lf.le_succ(p)

def lf.le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      lf.le_zero(c)
    case 1n+p 0n c:
      LAWire.wu_absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LAWire.wu_absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      lf.le_trans(p, q, r, ab, bc)

# Digits
# ------

# more fuel counts no fewer digits
def lf.go_fuel(+f: Nat, +g: Nat, +q: Nat, h: {Nat.is_le(f, g) == True{} : Bool}) -> {Nat.is_le(LawsBase.wire_digits.go(f, q), LawsBase.wire_digits.go(g, q)) == True{} : Bool}:
  match f g:
    case 0n g:
      lf.le_zero(LawsBase.wire_digits.go(g, q))
    case 1n+a 0n:
      LAWire.wu_absurd({Nat.is_le(LawsBase.wire_digits.go(1n+a, q), LawsBase.wire_digits.go(0n, q)) == True{} : Bool}, h)
    case 1n+a 1n+b:
      match q:
        case 0n:
          {==}
        case 1n+p:
          +m = {1n+p : Nat}
          lf.go_fuel(a, b, Nat.div(m, 10n), h)

# with the same fuel, a higher part no larger counts no more digits
def lf.go_mono(+f: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(LawsBase.wire_digits.go(f, a), LawsBase.wire_digits.go(f, b)) == True{} : Bool}:
  match f a b:
    case 0n a b:
      {==}
    case 1n+g 0n b:
      lf.le_zero(LawsBase.wire_digits.go(1n+g, b))
    case 1n+g 1n+p 0n:
      LAWire.wu_absurd({Nat.is_le(LawsBase.wire_digits.go(1n+g, 1n+p), 0n) == True{} : Bool}, h)
    case 1n+g 1n+p 1n+r:
      +m = {1n+p : Nat}
      +k = {1n+r : Nat}
      lf.go_mono(g, Nat.div(m, 10n), Nat.div(k, 10n), PWireU32RoundTrip.wu_div_mono(m, k, h))

# a Nat no larger has no more digits
def lf.digits_mono(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(LawsBase.wire_digits(a), LawsBase.wire_digits(b)) == True{} : Bool}:
  lf.le_trans(LawsBase.wire_digits.go(a, Nat.div(a, 10n)), LawsBase.wire_digits.go(b, Nat.div(a, 10n)), LawsBase.wire_digits.go(b, Nat.div(b, 10n)), lf.go_fuel(a, b, Nat.div(a, 10n), h), lf.go_mono(b, Nat.div(a, 10n), Nat.div(b, 10n), PWireU32RoundTrip.wu_div_mono(a, b, h)))

# Fits
# ----

# a Nat no larger than one that fits fits
def lf.fits_le(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}) -> {LawsBase.wire_fits(a) == True{} : Bool}:
  lf.le_trans(LawsBase.wire_digits(a), LawsBase.wire_digits(b), 14n, lf.digits_mono(a, b, h), fb)

# one less than a Nat that fits fits
def lf.fits_pred(+p: Nat, h: {LawsBase.wire_fits(1n+p) == True{} : Bool}) -> {LawsBase.wire_fits(p) == True{} : Bool}:
  lf.fits_le(p, 1n+p, lf.le_succ(p), h)

# one automatic iteration fewer fits
def lf.less_fits(l: Maybe<&2, Nat>, h: {LawsBase.wire_mfits(l) == True{} : Bool}) -> {LawsBase.wire_mfits(Lp.less(l)) == True{} : Bool}:
  match l:
    case None{}:
      {==}
    case Some{n}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          lf.fits_pred(p, h)

# The deadline of a span
# ----------------------

# the code's digit count is the wire's
def lf.go_eq(+f: Nat, +q: Nat) -> {Lp.digits.go(f, q) == LawsBase.wire_digits.go(f, q) : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match q:
        case 0n:
          {==}
        case 1n+p:
          +m = {1n+p : Nat}
          Equal.cong(Nat, Nat, v => 1n+v, Lp.digits.go(g, Nat.div(m, 10n)), LawsBase.wire_digits.go(g, Nat.div(m, 10n)), lf.go_eq(g, Nat.div(m, 10n)))

# the code's test of the wire is the wire's
def lf.fits_eq(+n: Nat) -> {Lp.fits(n) == LawsBase.wire_fits(n) : Bool}:
  Equal.cong(Nat, Bool, v => Nat.is_le(1n+v, 14n), Lp.digits.go(n, Nat.div(n, 10n)), LawsBase.wire_digits.go(n, Nat.div(n, 10n)), lf.go_eq(n, Nat.div(n, 10n)))

def lf.cut_fits.at(b: Bool, +t: Nat, e: {Lp.fits(t) == b : Bool}) -> {LawsBase.wire_mfits(Lp.until.cut(b, t)) == True{} : Bool}:
  match b:
    case True{}:
      Equal.trans(Bool, LawsBase.wire_fits(t), Lp.fits(t), True{}, Equal.sym(Bool, Lp.fits(t), LawsBase.wire_fits(t), lf.fits_eq(t)), e)
    case False{}:
      {==}

# the deadline of a span fits the wire, or there is none
def lf.cut_fits(+t: Nat) -> {LawsBase.wire_mfits(Lp.until.cut(Lp.fits(t), t)) == True{} : Bool}:
  lf.cut_fits.at(Lp.fits(t), t, {==})

def lf.cut_at(b: Bool, -t: Nat) -> {Lp.until.cut(b, t) == Loop.lp_cut.at(b, t) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the deadline of a span is the law's (Loop.lp_cut)
def lf.cut_eq(+t: Nat) -> {Lp.until.cut(Lp.fits(t), t) == Loop.lp_cut(t) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Lp.fits(t), LawsBase.wire_fits(t), lf.fits_eq(t)) : {Lp.until.cut(_, t) == Loop.lp_cut.at(LawsBase.wire_fits(t), t) : Maybe<&2, Nat>}
  lf.cut_at(LawsBase.wire_fits(t), t)
