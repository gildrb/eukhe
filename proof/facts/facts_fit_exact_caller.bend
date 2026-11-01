# eukhe: the proof of LAW facts_fit_exact_caller

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts
import ./base.bend as LA

def Facts.facts_fit_exact_caller(x, mm, b, a, win):
  %LA.w2.cap_sum(x, mm, b) : {Fx.fit(Some{x}, mm, b, a, win) == Facts.budgets.fit(Fx.cap.shrink(_, win), b, a) : Fx.Fit}
  {==}
