# eukhe: the proof of LAW tui_effort_ramp_length

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

def pu.length_go(+left: Nat, +done: Nat, +lo: TC.Px, +hi: TC.Px, +n: Nat) -> {List.length(&2, TC.Px, TC.ramp.go(left, done, lo, hi, n)) == left : Nat}:
  match left:
    case 0n:
      {==}
    case 1n+l:
      %pu.length_go(l, 1n+done, lo, hi, n) : {1n+List.length(&2, TC.Px, TC.ramp.go(l, 1n+done, lo, hi, n)) == 1n+_ : Nat}
      {==}

def tui_effort_ramp_length(+lo: TC.Px, +hi: TC.Px, +n: Nat) -> {List.length(&2, TC.Px, TC.ramp(lo, hi, n)) == n : Nat}:
  pu.length_go(n, 0n, lo, hi, n)

# (T3) Terminal colors

def TuiColor.tui_effort_ramp_length(lo, hi, n):
  tui_effort_ramp_length(lo, hi, n)
