# eukhe: the proof of LAW tui_effort_ramp_exact
# ramp.go(1 + l, done) holds, at index k <= l, the rung with w = done + 1
# + k rising and l - k falling (rex.go, by induction on k); for the whole
# ramp (done 0, n = 1 + l) that is n - (k + 1) falling, the spec's rung
# (rex.rung, channel by channel on the direction of each channel).

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def rex.rung3(+u1: Bool, +u2: Bool, +u3: Bool, +lr: Nat, +lg: Nat, +lb: Nat, +hr: Nat, +hg: Nat, +hb: Nat, +k: Nat, +l: Nat)
  -> {TC.Px{TC.chan.pick(u1, lr, hr, 1n+k, Nat.sub(l, k), 1n+l), TC.chan.pick(u2, lg, hg, 1n+k, Nat.sub(l, k), 1n+l), TC.chan.pick(u3, lb, hb, 1n+k, Nat.sub(l, k), 1n+l)}
      == TC.Px{TuiColor.chan_spec.pick(u1, lr, hr, 1n+k, 1n+l), TuiColor.chan_spec.pick(u2, lg, hg, 1n+k, 1n+l), TuiColor.chan_spec.pick(u3, lb, hb, 1n+k, 1n+l)} : TC.Px}:
  match u1 u2 u3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the rung with w = k + 1 rising and l - k falling, of a ramp of 1 + l
# rungs, is the spec's rung k + 1
def rex.rung(+lo: TC.Px, +hi: TC.Px, +k: Nat, +l: Nat) -> {TC.rung(lo, hi, 1n+k, Nat.sub(l, k), 1n+l) == TuiColor.rung_spec(lo, hi, 1n+k, 1n+l) : TC.Px}:
  match lo hi:
    case TC.Px{lr, lg, lb} TC.Px{hr, hg, hb}:
      rex.rung3(Nat.is_le(lr, hr), Nat.is_le(lg, hg), Nat.is_le(lb, hb), lr, lg, lb, hr, hg, hb, k, l)

# index k (at most l) of the rungs after the first done ones, 1 + l of
# them to go
def rex.go(+k: Nat, +l: Nat, +done: Nat, +lo: TC.Px, +hi: TC.Px, +n: Nat, +le: {Nat.is_le(k, l) == True{} : Bool})
  -> {List.get(&2, TC.Px, TC.ramp.go(1n+l, done, lo, hi, n), k) == Some{TC.rung(lo, hi, 1n+Nat.add(done, k), Nat.sub(l, k), n)} : Maybe<&2, TC.Px>}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(done, 0n), done, LNat.pa.add_zero(done)) : {List.get(&2, TC.Px, TC.ramp.go(1n+l, done, lo, hi, n), 0n) == Some{TC.rung(lo, hi, 1n+_, Nat.sub(l, 0n), n)} : Maybe<&2, TC.Px>}
      %LNat.pj.sub_zero(l) : {List.get(&2, TC.Px, TC.ramp.go(1n+l, done, lo, hi, n), 0n) == Some{TC.rung(lo, hi, 1n+done, _, n)} : Maybe<&2, TC.Px>}
      {==}
    case 1n+j:
      match l:
        case 0n:
          LLogicLogic.pu.absurd_ft({List.get(&2, TC.Px, TC.ramp.go(1n, done, lo, hi, n), 1n+j) == Some{TC.rung(lo, hi, 1n+Nat.add(done, 1n+j), Nat.sub(0n, 1n+j), n)} : Maybe<&2, TC.Px>}, le)
        case 1n+m:
          %LNat.add_succ_r(done, j) : {List.get(&2, TC.Px, TC.ramp.go(1n+m, 1n+done, lo, hi, n), j) == Some{TC.rung(lo, hi, 1n+_, Nat.sub(m, j), n)} : Maybe<&2, TC.Px>}
          rex.go(j, m, 1n+done, lo, hi, n, le)

def TuiColor.tui_effort_ramp_exact(lo, hi, n, k, lt):
  match n:
    case 0n:
      LLogicLogic.pu.absurd_ft({List.get(&2, TC.Px, TC.ramp(lo, hi, 0n), k) == Some{TuiColor.rung_spec(lo, hi, 1n+k, 0n)} : Maybe<&2, TC.Px>}, Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, LNat.pu.lt_zero_f(k), lt))
    case 1n+l:
      %rex.rung(lo, hi, k, l) : {List.get(&2, TC.Px, TC.ramp(lo, hi, 1n+l), k) == Some{_} : Maybe<&2, TC.Px>}
      rex.go(k, l, 0n, lo, hi, 1n+l, LA.pu.le_succ_of_lt(k, 1n+l, lt))
