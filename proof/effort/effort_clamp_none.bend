# eukhe: the proof of LAW effort_clamp_none
# The clamp over no offered level scans every level and finds none: off
# (LA.pe.clamp_nil).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

def Effort.effort_clamp_none(m, l, none):
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), [], none) : {Ef.clamp.in(_, l) == Ef.Off{} : Ef.Lv}
  LA.pe.clamp_nil(l)
