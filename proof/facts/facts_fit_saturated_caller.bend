# eukhe: the proof of LAW facts_fit_saturated_caller

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# b - c is 0 when b is at most c
def w2.sub_zero_le(+b: Nat, +c: Nat, h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.sub(b, c) == 0n : Nat}:
  match b c:
    case 0n c:
      {==}
    case 1n+p 0n:
      L.pq.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      w2.sub_zero_le(p, q, h)

# with a cap of mm or more, the ceiling is mm
def w2.cap_above(+x: Nat, +mm: Nat, +b: Nat, h: {Nat.is_le(mm, x) == True{} : Bool}) -> {Fx.fit.cap(Some{x}, mm, b) == mm : Nat}:
  %Equal.sym(Nat, Nat.sub(mm, x), 0n, w2.sub_zero_le(mm, x, h)) : {Fx.fit.cap.add(Nat.is_lt(b, _), x, mm, b) == mm : Nat}
  %Equal.sym(Bool, Nat.is_lt(b, 0n), False{}, LA.w2.lt_zero(b)) : {Fx.fit.cap.add(_, x, mm, b) == mm : Nat}
  {==}

def Laws.facts_fit_saturated_caller(x, mm, b, a, above):
  %w2.cap_above(x, mm, b, above) : {Fx.fit(Some{x}, mm, b, a) == Fx.fit.at(Nat.is_le(_, b), _, b, a) : Fx.Fit}
  {==}
