# eukhe: the proof of LAW effort_offered_wired
# A wire entry passes the filter's test, and a level of the ladder that
# passes it is offered (LA.pe.ladder_kept).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

def Effort.effort_offered_wired(map, l, wire):
  LA.pe.ladder_kept(map, l, Equal.cong(Ef.Ent, Bool, e => Ef.keep.e(l, e), Ef.entry(l, map), Ef.Wire{}, wire))
