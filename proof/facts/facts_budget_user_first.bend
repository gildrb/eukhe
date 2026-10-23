# eukhe: the proof of LAW facts_budget_user_first

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def Facts.facts_budget_user_first(c, d, l, n, u):
  %Equal.sym(Maybe<&2, Nat>, Fx.Customs.at(c, l), Some{n}, u) : {Maybe.default(&2, Nat, _, Fx.Budgets.at(d, l)) == n : Nat}
  {==}
