# eukhe: the proof of LAW pace_lag_at_cap

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base/logic/logic.bend as LLogicLogic

# b <= k: k is not below b
def ps.le_not_lt(b: Nat, k: Nat, h: {Nat.is_le(b, k) == True{} : Bool}) -> {Nat.is_lt(k, b) == False{} : Bool}:
  match b k:
    case 0n _:
      match k:
        case 0n:
          {==}
        case 1n+kp:
          {==}
    case 1n+bp 0n:
      LLogicLogic.screen.ps.absurdF({Nat.is_lt(0n, 1n+bp) == False{} : Bool}, h)
    case 1n+bp 1n+kp:
      ps.le_not_lt(bp, kp, h)

def ps.max_zero(m: Nat) -> {Nat.max(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ps.pace_lag_at_cap(+min: Nat, +k: Nat, +b: Nat, capped: {Nat.is_le(b, k) == True{} : Bool}) -> {Sc.reveal(min, k, b) == Nat.min(b, min) : Nat}:
  %Equal.sym(Bool, Nat.is_lt(k, b), False{}, ps.le_not_lt(b, k, capped)) : {Nat.min(b, Nat.max(min, Sc.share.at(_, k, b))) == Nat.min(b, min) : Nat}
  %Equal.sym(Nat, Nat.max(min, 0n), min, ps.max_zero(min)) : {Nat.min(b, _) == Nat.min(b, min) : Nat}
  {==}

def Screen.pace_lag_at_cap(min, k, b, capped):
  ps.pace_lag_at_cap(min, k, b, capped)
