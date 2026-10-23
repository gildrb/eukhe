# eukhe: the proof of LAW facts_google_unordered_refused

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def Facts.facts_google_unordered_refused(b, c, l, bad):
  %Equal.sym(Bool, Fx.Budgets.ordered(b), False{}, bad) : {Fx.gbudget.rule(_, b, c, l) == Fx.Unordered{} : Fx.GB}
  {==}
