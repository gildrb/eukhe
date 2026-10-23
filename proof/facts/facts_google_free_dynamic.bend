# eukhe: the proof of LAW facts_google_free_dynamic

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def Facts.facts_google_free_dynamic(c, l, u):
  %Equal.sym(Maybe<&2, Nat>, Fx.Customs.at(c, l), None{}, u) : {Fx.gbudget.free(_) == Fx.Dynamic{} : Fx.GB}
  {==}
