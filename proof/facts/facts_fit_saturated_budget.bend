# eukhe: the proof of LAW facts_fit_saturated_budget

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ../base/bool/misc.bend as LBoolMisc
import ./base.bend as LA

# y at most b: b is not below y
def w2.le_not_lt(+y: Nat, +b: Nat, h: {Nat.is_le(y, b) == True{} : Bool}) -> {Nat.is_lt(b, y) == False{} : Bool}:
  match y b:
    case 0n b:
      LA.w2.lt_zero(b)
    case 1n+p 0n:
      LBoolMisc.pq.absurdF({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      w2.le_not_lt(p, q, h)

# a budget of mm or more fills the ceiling mm
def w2.cap_budget(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, h: {Nat.is_le(mm, b) == True{} : Bool}) -> {Fx.fit.cap(base, mm, b) == mm : Nat}:
  match base:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Bool, Nat.is_lt(b, Nat.sub(mm, x)), False{}, w2.le_not_lt(Nat.sub(mm, x), b, LA.pf.le_trans(Nat.sub(mm, x), mm, b, LA.pf.sub_le(mm, x), h))) : {Fx.fit.cap.add(_, x, mm, b) == mm : Nat}
      {==}

def w2.fit_full(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat, +h: {Nat.is_le(mm, b) == True{} : Bool}) -> {Fx.fit(base, mm, b, a) == Fx.Fit{mm, Nat.sub(mm, a)} : Fx.Fit}:
  %Equal.sym(Nat, Fx.fit.cap(base, mm, b), mm, w2.cap_budget(base, mm, b, h)) : {Fx.fit.at(Nat.is_le(_, b), _, b, a) == Fx.Fit{mm, Nat.sub(mm, a)} : Fx.Fit}
  %Equal.sym(Bool, Nat.is_le(mm, b), True{}, h) : {Fx.fit.at(_, mm, b, a) == Fx.Fit{mm, Nat.sub(mm, a)} : Fx.Fit}
  %Equal.sym(Nat, Nat.min(b, Nat.sub(mm, a)), Nat.sub(mm, a), LA.w2.min_r(b, Nat.sub(mm, a), LA.pf.le_trans(Nat.sub(mm, a), mm, b, LA.pf.sub_le(mm, a), h))) : {Fx.Fit{mm, _} == Fx.Fit{mm, Nat.sub(mm, a)} : Fx.Fit}
  {==}

def Facts.facts_fit_saturated_budget(base, mm, b1, b2, a, h1, h2):
  Equal.trans(Fx.Fit, Fx.fit(base, mm, b1, a), Fx.Fit{mm, Nat.sub(mm, a)}, Fx.fit(base, mm, b2, a), w2.fit_full(base, mm, b1, a, h1), Equal.sym(Fx.Fit, Fx.fit(base, mm, b2, a), Fx.Fit{mm, Nat.sub(mm, a)}, w2.fit_full(base, mm, b2, a, h2)))
