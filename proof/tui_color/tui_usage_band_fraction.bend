# eukhe: the proof of LAW tui_usage_band_fraction

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor
import ./base.bend as LA

def pu.pos(+k: Nat, +w: Nat) -> {Nat.is_lt(0n, Nat.mul(1n+k, w)) == Nat.is_lt(0n, w) : Bool}:
  match w:
    case 0n:
      %Equal.sym(Nat, Nat.mul(k, 0n), 0n, LA.pu.mul_zero_r(k)) : {Nat.is_lt(0n, _) == Nat.is_lt(0n, 0n) : Bool}
      {==}
    case 1n+v:
      {==}

def pu.lt_add_both(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  LA.pu.lt_of_le_succ(Nat.add(a, c), Nat.add(b, d), LA.pu.le_add_both(1n+a, b, c, d, LA.pu.le_succ_of_lt(a, b, ab), cd))

def pu.mul_lt_mono(+k: Nat, +x: Nat, +y: Nat, +h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(1n+k, x), Nat.mul(1n+k, y)) == True{} : Bool}:
  pu.lt_add_both(x, y, Nat.mul(k, x), Nat.mul(k, y), h, LA.pu.mul_le_mono_r(k, x, y, LA.pu.lt_le(x, y, h)))

def pu.cancel.pick(+b: Bool, +k: Nat, +x: Nat, +y: Nat, +eb: {Nat.is_le(x, y) == b : Bool}) -> {Nat.is_le(Nat.mul(1n+k, x), Nat.mul(1n+k, y)) == b : Bool}:
  match b:
    case True{}:
      LA.pu.mul_le_mono_r(1n+k, x, y, eb)
    case False{}:
      LA.pu.lt_not_le(Nat.mul(1n+k, y), Nat.mul(1n+k, x), pu.mul_lt_mono(k, y, x, LA.pu.not_le_lt(x, y, eb)))

# a factor 1 + k on both sides of <= cancels
def pu.cancel(+k: Nat, +x: Nat, +y: Nat) -> {Nat.is_le(Nat.mul(1n+k, x), Nat.mul(1n+k, y)) == Nat.is_le(x, y) : Bool}:
  pu.cancel.pick(Nat.is_le(x, y), k, x, y, {==})

# a band is reached by the same fraction of any window
def pu.reach_scale(+f: TC.Frac, +k: Nat, +t: Nat, +w: Nat) -> {TC.reached(f, Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.reached(f, t, w) : Bool}:
  match f:
    case TC.Frac{num, den}:
      +kk = {1n+k : Nat}
      +rhs = Bool.and(Nat.is_lt(0n, w), Nat.is_le(Nat.mul(w, num), Nat.mul(t, den)))
      %Equal.sym(Bool, Nat.is_lt(0n, Nat.mul(kk, w)), Nat.is_lt(0n, w), pu.pos(k, w)) : {Bool.and(_, Nat.is_le(Nat.mul(Nat.mul(kk, w), num), Nat.mul(Nat.mul(kk, t), den))) == rhs : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.mul(kk, w), num), Nat.mul(kk, Nat.mul(w, num)), LA.pu.mul_assoc(kk, w, num)) : {Bool.and(Nat.is_lt(0n, w), Nat.is_le(_, Nat.mul(Nat.mul(kk, t), den))) == rhs : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.mul(kk, t), den), Nat.mul(kk, Nat.mul(t, den)), LA.pu.mul_assoc(kk, t, den)) : {Bool.and(Nat.is_lt(0n, w), Nat.is_le(Nat.mul(kk, Nat.mul(w, num)), _)) == rhs : Bool}
      %Equal.sym(Bool, Nat.is_le(Nat.mul(kk, Nat.mul(w, num)), Nat.mul(kk, Nat.mul(t, den))), Nat.is_le(Nat.mul(w, num), Nat.mul(t, den)), pu.cancel(k, Nat.mul(w, num), Nat.mul(t, den))) : {Bool.and(Nat.is_lt(0n, w), _) == rhs : Bool}
      {==}

def pu.band_scale(+fs: List<&2, TC.Frac>, +k: Nat, +t: Nat, +w: Nat) -> {TC.band.go(fs, Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.band.go(fs, t, w) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, rest}:
      +kt = Nat.mul(1n+k, t)
      +kw = Nat.mul(1n+k, w)
      %pu.band_scale(rest, k, t, w) : {Nat.add(TC.one(TC.reached(f, kt, kw)), TC.band.go(rest, kt, kw)) == Nat.add(TC.one(TC.reached(f, t, w)), _) : Nat}
      %pu.reach_scale(f, k, t, w) : {Nat.add(TC.one(TC.reached(f, kt, kw)), TC.band.go(rest, kt, kw)) == Nat.add(TC.one(_), TC.band.go(rest, kt, kw)) : Nat}
      {==}

def tui_usage_band_fraction(+k: Nat, +t: Nat, +w: Nat) -> {TC.band(Nat.mul(1n+k, t), Nat.mul(1n+k, w)) == TC.band(t, w) : Nat}:
  pu.band_scale(TC.bands(), k, t, w)

def TuiColor.tui_usage_band_fraction(k, t, w):
  tui_usage_band_fraction(k, t, w)
