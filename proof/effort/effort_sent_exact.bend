# eukhe: the proof of LAW effort_sent_exact
# The fallback is es.or's, and the fit es.fit's (LA.ps.fit).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def pss.sent(s: Ef.Sess) -> {Ef.sent(s) == Effort.es.sent(s) : Ef.Lv}:
  match s:
    case Ef.Sess{+mo, +st}:
      %LA.ps.or(st, Ef.Off{}) : {Ef.fit(mo, Maybe.default(&2, Ef.Lv, st, Ef.Off{})) == Effort.es.fit(mo, _) : Ef.Lv}
      LA.ps.fit(mo, Maybe.default(&2, Ef.Lv, st, Ef.Off{}))

def Effort.effort_sent_exact(s):
  pss.sent(s)
