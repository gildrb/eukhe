# eukhe: the proof of LAW tui_usage_band_monotone

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor
import ../base/nat.bend as LNat
import ./base.bend as LA

# t * den <= (t + e) * den
def pu.mul_le_add(+t: Nat, +e: Nat, +den: Nat) -> {Nat.is_le(Nat.mul(t, den), Nat.mul(Nat.add(t, e), den)) == True{} : Bool}:
  match t:
    case 0n:
      LNat.pu.le_zero(Nat.mul(e, den))
    case 1n+p:
      LA.pu.le_add_l(den, Nat.mul(p, den), Nat.mul(Nat.add(p, e), den), pu.mul_le_add(p, e, den))

def pu.one_and(+p: Bool, +x: Bool, +y: Bool, hxy: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Nat.is_le(TC.one(Bool.and(p, x)), TC.one(Bool.and(p, y))) == True{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      match x:
        case True{}:
          %Equal.sym(Bool, y, True{}, hxy({==})) : {Nat.is_le(1n, TC.one(_)) == True{} : Bool}
          {==}
        case False{}:
          LNat.pu.le_zero(TC.one(y))

# a band reached by t tokens stays reached by t + e
def pu.reach_mono(+f: TC.Frac, +t: Nat, +e: Nat, +w: Nat) -> {Nat.is_le(TC.one(TC.reached(f, t, w)), TC.one(TC.reached(f, Nat.add(t, e), w))) == True{} : Bool}:
  match f:
    case TC.Frac{num, den}:
      +lhs = Nat.mul(w, num)
      pu.one_and(Nat.is_lt(0n, w), Nat.is_le(lhs, Nat.mul(t, den)), Nat.is_le(lhs, Nat.mul(Nat.add(t, e), den)), ex => LNat.pu.le_trans(lhs, Nat.mul(t, den), Nat.mul(Nat.add(t, e), den), ex, pu.mul_le_add(t, e, den)))

def pu.band_mono(+fs: List<&2, TC.Frac>, +t: Nat, +e: Nat, +w: Nat) -> {Nat.is_le(TC.band.go(fs, t, w), TC.band.go(fs, Nat.add(t, e), w)) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, rest}:
      LA.pu.le_add_both(TC.one(TC.reached(f, t, w)), TC.one(TC.reached(f, Nat.add(t, e), w)), TC.band.go(rest, t, w), TC.band.go(rest, Nat.add(t, e), w), pu.reach_mono(f, t, e, w), pu.band_mono(rest, t, e, w))

def tui_usage_band_monotone(+t: Nat, +e: Nat, +w: Nat) -> {Nat.is_le(TC.band(t, w), TC.band(Nat.add(t, e), w)) == True{} : Bool}:
  pu.band_mono(TC.bands(), t, e, w)

def TuiColor.tui_usage_band_monotone(t, e, w):
  tui_usage_band_monotone(t, e, w)
