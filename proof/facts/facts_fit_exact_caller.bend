# eukhe: the proof of LAW facts_fit_exact_caller

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.facts_fit_exact_caller(x, mm, b, a):
  %LA.w2.cap_sum(x, mm, b) : {Fx.fit(Some{x}, mm, b, a) == Laws.budgets.fit(_, b, a) : Fx.Fit}
  +K = Fx.fit.cap(Some{x}, mm, b)
  LA.w2.fit_at(Nat.is_le(K, b), K, b, a)
