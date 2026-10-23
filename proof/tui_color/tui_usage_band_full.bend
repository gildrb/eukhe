# eukhe: the proof of LAW tui_usage_band_full

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor
import ../base.bend as L
import ./base.bend as LA

# tokens past the window reach a band of num <= den as the full window
# does: w * num <= w * den <= t * den
def pu.reach_full(+num: Nat, +den: Nat, +t: Nat, +w: Nat, +hnd: {Nat.is_le(num, den) == True{} : Bool}, +past: {Nat.is_le(w, t) == True{} : Bool}) -> {TC.reached(TC.Frac{num, den}, t, w) == TC.reached(TC.Frac{num, den}, w, w) : Bool}:
  +wn = Nat.mul(w, num)
  +a = LA.pu.mul_le_mono_r(w, num, den, hnd)
  +c = L.pu.le_trans(wn, Nat.mul(w, den), Nat.mul(t, den), a, LA.pu.mul_le_mono_l(w, t, den, past))
  %Equal.sym(Bool, Nat.is_le(wn, Nat.mul(t, den)), True{}, c) : {Bool.and(Nat.is_lt(0n, w), _) == Bool.and(Nat.is_lt(0n, w), Nat.is_le(wn, Nat.mul(w, den))) : Bool}
  %Equal.sym(Bool, Nat.is_le(wn, Nat.mul(w, den)), True{}, a) : {Bool.and(Nat.is_lt(0n, w), True{}) == Bool.and(Nat.is_lt(0n, w), _) : Bool}
  {==}

def TuiColor.tui_usage_band_full(t, w, past):
  +f1 = {TC.Frac{1n, 2n} : TC.Frac}
  +f2 = {TC.Frac{7n, 10n} : TC.Frac}
  +f3 = {TC.Frac{9n, 10n} : TC.Frac}
  +r1 = TC.reached(f1, w, w)
  +r2 = TC.reached(f2, w, w)
  +r3 = TC.reached(f3, w, w)
  %Equal.sym(Bool, TC.reached(f1, t, w), r1, pu.reach_full(1n, 2n, t, w, {==}, past)) : {Nat.add(TC.one(_), Nat.add(TC.one(TC.reached(f2, t, w)), Nat.add(TC.one(TC.reached(f3, t, w)), 0n))) == TC.band(w, w) : Nat}
  %Equal.sym(Bool, TC.reached(f2, t, w), r2, pu.reach_full(7n, 10n, t, w, {==}, past)) : {Nat.add(TC.one(r1), Nat.add(TC.one(_), Nat.add(TC.one(TC.reached(f3, t, w)), 0n))) == TC.band(w, w) : Nat}
  %Equal.sym(Bool, TC.reached(f3, t, w), r3, pu.reach_full(9n, 10n, t, w, {==}, past)) : {Nat.add(TC.one(r1), Nat.add(TC.one(r2), Nat.add(TC.one(_), 0n))) == TC.band(w, w) : Nat}
  {==}
