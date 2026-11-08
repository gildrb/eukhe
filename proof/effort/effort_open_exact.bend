# eukhe: the proof of LAW effort_open_exact
# The default is es.or's, and the fit es.fit's (LA.ps.fit: the model's
# clamp is the laws' over es.lad).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/entry.bend as EffortEntry
import ./base.bend as LA

def pso.open(s: Ef.Sess, +dflt: Ef.Lv) -> {Ef.open(s, dflt) == EffortEntry.es.open(s, dflt) : Ef.Sess}:
  match s:
    case Ef.Sess{+mo, +st}:
      +l = Maybe.default(&2, Ef.Lv, st, dflt)
      %LA.ps.or(st, dflt) : {Ef.Sess{mo, Some{Ef.fit(mo, l)}} == Ef.Sess{mo, Some{EffortEntry.es.fit(mo, _)}} : Ef.Sess}
      %LA.ps.fit(mo, l) : {Ef.Sess{mo, Some{Ef.fit(mo, l)}} == Ef.Sess{mo, Some{_}} : Ef.Sess}
      {==}

def EffortEntry.effort_open_exact(s, dflt):
  pso.open(s, dflt)
