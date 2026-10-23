# eukhe: the proof of LAW facts_google_free_user

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws

def Laws.facts_google_free_user(c, l, n, u):
  %Equal.sym(Maybe<&2, Nat>, Fx.Customs.at(c, l), Some{n}, u) : {Fx.gbudget.free(_) == Fx.Tokens{n} : Fx.GB}
  {==}
