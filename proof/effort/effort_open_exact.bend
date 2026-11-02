# eukhe: the proof of LAW effort_open_exact
# The default is es.or's, and the fit es.fit's (LA.ps.fit: the model's
# clamp is the laws' over es.lad).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def pso.open(s: Ef.Sess, +dflt: Ef.Lv) -> {Ef.open(s, dflt) == Effort.es.open(s, dflt) : Ef.Sess}:
  match s:
    case Ef.Sess{+mo, +st}:
      +l = Maybe.default(&2, Ef.Lv, st, dflt)
      %LA.ps.or(st, dflt) : {Ef.Sess{mo, Some{Ef.fit(mo, l)}} == Ef.Sess{mo, Some{Effort.es.fit(mo, _)}} : Ef.Sess}
      %LA.ps.fit(mo, l) : {Ef.Sess{mo, Some{Ef.fit(mo, l)}} == Ef.Sess{mo, Some{_}} : Ef.Sess}
      {==}

def Effort.effort_open_exact(s, dflt):
  pso.open(s, dflt)
