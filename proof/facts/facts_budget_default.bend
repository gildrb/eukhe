# eukhe: the proof of LAW facts_budget_default

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def Facts.facts_budget_default(c, d, l, u):
  %Equal.sym(Maybe<&2, Nat>, Fx.Customs.at(c, l), None{}, u) : {Maybe.default(&2, Nat, _, Fx.Budgets.at(d, l)) == Fx.Budgets.at(d, l) : Nat}
  {==}
