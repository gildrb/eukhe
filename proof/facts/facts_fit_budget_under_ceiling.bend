# eukhe: the proof of LAW facts_fit_budget_under_ceiling

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ./base.bend as LA

def pf.facts_fit_budget_under_ceiling(+base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat, +win: Fx.Win) -> {Nat.is_le(Fx.Fit.budget(Fx.fit(base, mm, b, a, win)), Fx.Fit.max(Fx.fit(base, mm, b, a, win))) == True{} : Bool}:
  +m = Fx.cap.shrink(Fx.fit.cap(base, mm, b), win)
  LA.pf.le_trans(Nat.min(b, Nat.sub(m, a)), Nat.sub(m, a), m, LA.pf.min_le_r(b, Nat.sub(m, a)), LA.pf.sub_le(m, a))

def Facts.facts_fit_budget_under_ceiling(base, mm, b, a, win):
  pf.facts_fit_budget_under_ceiling(base, mm, b, a, win)
