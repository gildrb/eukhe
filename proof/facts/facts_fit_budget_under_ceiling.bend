# eukhe: the proof of LAW facts_fit_budget_under_ceiling

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# a not at most b: b is at most a
def pf.not_le_le(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      LLogicLogic.pq.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      LLogicLogic.pq.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.not_le_le(p, q, h)

def pf.fit_at_le(+m: Nat, +b: Nat, +a: Nat, c: Bool, ec: {Nat.is_le(m, b) == c : Bool}) -> {Nat.is_le(Fx.Fit.budget(Fx.fit.at(c, m, b, a)), Fx.Fit.max(Fx.fit.at(c, m, b, a))) == True{} : Bool}:
  match c:
    case True{}:
      LA.pf.le_trans(Nat.min(b, Nat.sub(m, a)), Nat.sub(m, a), m, LA.pf.min_le_r(b, Nat.sub(m, a)), LA.pf.sub_le(m, a))
    case False{}:
      pf.not_le_le(m, b, ec)

def pf.facts_fit_budget_under_ceiling(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat) -> {Nat.is_le(Fx.Fit.budget(Fx.fit(base, mm, b, a)), Fx.Fit.max(Fx.fit(base, mm, b, a))) == True{} : Bool}:
  +m = Fx.fit.cap(base, mm, b)
  pf.fit_at_le(m, b, a, Nat.is_le(m, b), {==})

def Facts.facts_fit_budget_under_ceiling(base, mm, b, a):
  pf.facts_fit_budget_under_ceiling(base, mm, b, a)
