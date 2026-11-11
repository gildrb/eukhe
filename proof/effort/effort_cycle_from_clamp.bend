# eukhe: the proof of LAW effort_cycle_from_clamp
# Both steps start at the clamp of their level, and the clamp of a clamp
# is the clamp (LA.pe.clamp_idem).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

def cf.at(b: Bool, +lad: List<&2, Ef.Lv>, +l: Ef.Lv, d: Ef.Dir) -> {Ef.cycle.at(b, lad, l, d) == Ef.cycle.at(b, lad, Ef.clamp.in(lad, l), d) : Maybe<&2, Ef.Lv>}:
  match b:
    case True{}:
      %Equal.sym(Ef.Lv, Ef.clamp.in(lad, Ef.clamp.in(lad, l)), Ef.clamp.in(lad, l), LA.pe.clamp_idem(lad, l)) : {Ef.move(d, lad, Ef.clamp.in(lad, l)) == Ef.move(d, lad, _) : Maybe<&2, Ef.Lv>}
      {==}
    case False{}:
      {==}

def Effort.effort_cycle_from_clamp(m, l, d):
  cf.at(Ef.two(Ef.offered(m)), Ef.offered(m), l, d)
