# eukhe: the proof of LAW facts_google_ordered_tokens

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def Facts.facts_google_ordered_tokens(b, c, l, ok):
  %Equal.sym(Bool, Fx.Budgets.ordered(b), True{}, ok) : {Fx.gbudget.rule(_, b, c, l) == Fx.Tokens{Fx.gtokens(b, c, l)} : Fx.GB}
  {==}
