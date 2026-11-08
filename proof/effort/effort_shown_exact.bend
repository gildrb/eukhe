# eukhe: the proof of LAW effort_shown_exact
# No stored level shows `default`; a stored one is fitted as es.fit fits
# it (LA.ps.fit).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/entry.bend as EffortEntry
import ./base.bend as LA

def psw.shown(s: Ef.Sess) -> {Ef.shown(s) == EffortEntry.es.shown(s) : Ef.Shown}:
  match s:
    case Ef.Sess{+mo, st}:
      match st:
        case None{}:
          {==}
        case Some{+l}:
          %LA.ps.fit(mo, l) : {Ef.Level{Ef.fit(mo, l)} == Ef.Level{_} : Ef.Shown}
          {==}

def EffortEntry.effort_shown_exact(s):
  psw.shown(s)
