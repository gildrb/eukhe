# eukhe: the proof of LAW facts_fit_saturated_budget

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# y at most b: b is not below y
def w2.le_not_lt(+y: Nat, +b: Nat, h: {Nat.is_le(y, b) == True{} : Bool}) -> {Nat.is_lt(b, y) == False{} : Bool}:
  match y b:
    case 0n b:
      LA.w2.lt_zero(b)
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
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

# a budget of mm or more fits as the ceiling of mm through the window,
# all of it after the answer's tokens
def w2.fit_full(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat, +w: Nat, +p: Nat, +s: Nat, +f: Nat, +st: Bool, +h: {Nat.is_le(mm, b) == True{} : Bool}, +hf: {Nat.is_le(f, mm) == True{} : Bool}) -> {Fx.fit(base, mm, b, a, Fx.Win{w, p, s, f, st}) == Fx.Fit{Fx.cap.shrink(mm, Fx.Win{w, p, s, f, st}), Nat.sub(Fx.cap.shrink(mm, Fx.Win{w, p, s, f, st}), a)} : Fx.Fit}:
  +W = {Fx.Win{w, p, s, f, st} : Fx.Win}
  +M = Fx.cap.shrink(mm, W)
  +ml = LA.pf.le_trans(M, Nat.max(f, mm), mm, LA.pf.shrink_le(mm, w, p, s, f, st), LA.pf.max_le(f, mm, mm, hf, LA.facts.pf.le_refl(mm)))
  +le = LA.pf.le_trans(Nat.sub(M, a), mm, b, LA.pf.le_trans(Nat.sub(M, a), M, mm, LA.pf.sub_le(M, a), ml), h)
  %Equal.sym(Nat, Fx.fit.cap(base, mm, b), mm, w2.cap_budget(base, mm, b, h)) : {Fx.Fit{Fx.cap.shrink(_, W), Fx.room(b, Fx.cap.shrink(_, W), a)} == Fx.Fit{M, Nat.sub(M, a)} : Fx.Fit}
  %Equal.sym(Nat, Nat.min(b, Nat.sub(M, a)), Nat.sub(M, a), LA.w2.min_r(b, Nat.sub(M, a), le)) : {Fx.Fit{M, _} == Fx.Fit{M, Nat.sub(M, a)} : Fx.Fit}
  {==}

def Facts.facts_fit_saturated_budget(base, mm, b1, b2, a, w, p, s, f, st, h1, h2, hf):
  +W = {Fx.Win{w, p, s, f, st} : Fx.Win}
  +M = Fx.cap.shrink(mm, W)
  Equal.trans(Fx.Fit, Fx.fit(base, mm, b1, a, W), Fx.Fit{M, Nat.sub(M, a)}, Fx.fit(base, mm, b2, a, W), w2.fit_full(base, mm, b1, a, w, p, s, f, st, h1, hf), Equal.sym(Fx.Fit, Fx.fit(base, mm, b2, a, W), Fx.Fit{M, Nat.sub(M, a)}, w2.fit_full(base, mm, b2, a, w, p, s, f, st, h2, hf)))
