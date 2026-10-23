# eukhe: the proof of LAW run_rounds_lossless

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.lt_le(+m: Nat, +x: Nat, +e: {Nat.is_lt(x, m) == True{} : Bool}) -> {Nat.is_le(x, Nat.sub(m, 1n)) == True{} : Bool}:
  match m:
    case 0n:
      match x:
        case 0n:
          LA.rk.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, e)
        case 1n+y:
          LA.rk.absurd({Nat.is_le(1n+y, 0n) == True{} : Bool}, e)
    case 1n+v:
      %LA.rk.sub0(v) : {Nat.is_le(x, _) == True{} : Bool}
      Equal.trans(Bool, Nat.is_le(x, v), Nat.is_lt(x, 1n+v), True{}, LA.rk.lt_s(v, x), e)

def rk.run_rounds_lossless(+l: Rn.Lim, +count: Nat, +w: {Nat.is_lt(count, Rn.Lim.rounds(l)) == True{} : Bool}) -> {Nat.sub(Nat.sub(Rn.Lim.rounds(l), 1n), Rn.Lim.r(l, count)) == count : Nat}:
  match l:
    case Rn.Lim{+rounds, +wait, +retries, +most}:
      Equal.sym(Nat, count, Nat.sub(Nat.sub(rounds, 1n), Nat.sub(Nat.sub(rounds, 1n), count)), LA.rk.subsub(Nat.sub(rounds, 1n), count, rk.lt_le(rounds, count, w)))

def Run.run_rounds_lossless(l, count, w):
  rk.run_rounds_lossless(l, count, w)
