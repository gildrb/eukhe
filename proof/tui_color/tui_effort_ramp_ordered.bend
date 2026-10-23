# eukhe: the proof of LAW tui_effort_ramp_ordered

import Base
import ../../bend/tui_color.bend as TC
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# adding d never lowers the quotient
def pu.dv_le_add(+x: Nat, +d: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(Nat.div(x, n), Nat.div(Nat.add(d, x), n)) == True{} : Bool}:
  +y = Nat.add(d, x)
  +q = Nat.div(x, n)
  +low = L.pu.le_trans(Nat.mul(q, n), x, y, LA.pu.div_low(x, n, en), LA.pu.le_add(d, x))
  LA.pu.div_max(y, n, q, en, low)

# The effort ramp
# ---------------

# a channel never goes back from rung k to rung k + 1
def pu.chan_le(+u: Bool, +a: Nat, +b: Nat, +k: Nat, +l: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool})
  -> {TC.step.pick(u, TC.chan.pick(u, a, b, k, 1n+l, n), TC.chan.pick(u, a, b, 1n+k, l, n)) == True{} : Bool}:
  match u:
    case True{}:
      +d = Nat.sub(b, a)
      LA.pu.le_add_l(a, Nat.div(Nat.mul(k, d), n), Nat.div(Nat.add(d, Nat.mul(k, d)), n), pu.dv_le_add(Nat.mul(k, d), d, n, en))
    case False{}:
      +d = Nat.sub(a, b)
      LA.pu.le_add_l(b, Nat.div(Nat.mul(l, d), n), Nat.div(Nat.add(d, Nat.mul(l, d)), n), pu.dv_le_add(Nat.mul(l, d), d, n, en))

# the rungs after rung done move every channel on from it
def pu.ordered_go(+left: Nat, +done: Nat, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +n: Nat, +en: {Nat.is_le(1n, n) == True{} : Bool})
  -> {TC.ordered.from(TC.ramp.go(left, done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n), TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, done, left, n), TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}) == True{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+l:
      +sr = pu.chan_le(Nat.is_le(lr, hr), lr, hr, done, l, n, en)
      +sg = pu.chan_le(Nat.is_le(lg, hg), lg, hg, done, l, n, en)
      +sb = pu.chan_le(Nat.is_le(lb, hb), lb, hb, done, l, n, en)
      +here = L.pu.and_t(TC.step(lr, hr, TC.chan(lr, hr, done, 1n+l, n), TC.chan(lr, hr, 1n+done, l, n)), Bool.and(TC.step(lg, hg, TC.chan(lg, hg, done, 1n+l, n), TC.chan(lg, hg, 1n+done, l, n)), TC.step(lb, hb, TC.chan(lb, hb, done, 1n+l, n), TC.chan(lb, hb, 1n+done, l, n))), sr, L.pu.and_t(TC.step(lg, hg, TC.chan(lg, hg, done, 1n+l, n), TC.chan(lg, hg, 1n+done, l, n)), TC.step(lb, hb, TC.chan(lb, hb, done, 1n+l, n), TC.chan(lb, hb, 1n+done, l, n)), sg, sb))
      +more = pu.ordered_go(l, 1n+done, lr, lg, lb, hr, hg, hb, n, en)
      L.pu.and_t(TC.moves(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, done, 1n+l, n), TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+done, l, n)), TC.ordered.from(TC.ramp.go(l, 1n+done, TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, n), TC.rung(TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}, 1n+done, l, n), TC.Px{lr, lg, lb}, TC.Px{hr, hg, hb}), here, more)

def tui_effort_ramp_ordered(+lo: TC.Px, +hi: TC.Px, +n: Nat) -> {TC.ordered(lo, hi, TC.ramp(lo, hi, n)) == True{} : Bool}:
  match lo hi n:
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb} 0n:
      {==}
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb} 1n+m:
      pu.ordered_go(m, 1n, lr, lg, lb, hr, hg, hb, 1n+m, L.pu.le_zero(m))

def Laws.tui_effort_ramp_ordered(lo, hi, n):
  tui_effort_ramp_ordered(lo, hi, n)
