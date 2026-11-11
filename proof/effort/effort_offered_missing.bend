# eukhe: the proof of LAW effort_offered_missing
# A missing entry of a level below xhigh passes the filter's test (level by
# level), and a level of the ladder that passes it is offered.

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

# a level ranked under 5 is no xhigh or max
def pm.below(l: Ef.Lv, below: {Nat.is_lt(Effort.effort_rank(l), 5n) == True{} : Bool}) -> {Bool.not(Ef.ext(l)) == True{} : Bool}:
  match l:
    case Ef.Off{}:
      {==}
    case Ef.Minimal{}:
      {==}
    case Ef.Low{}:
      {==}
    case Ef.Medium{}:
      {==}
    case Ef.High{}:
      {==}
    case Ef.Xhigh{}:
      LA.pe.absurdF({Bool.not(Ef.ext(Ef.Xhigh{})) == True{} : Bool}, below)
    case Ef.Max{}:
      LA.pe.absurdF({Bool.not(Ef.ext(Ef.Max{})) == True{} : Bool}, below)

def Effort.effort_offered_missing(map, l, below, none):
  +k = Equal.trans(Bool, Ef.keep.e(l, Ef.entry(l, map)), Ef.keep.e(l, Ef.Missing{}), True{}, Equal.cong(Ef.Ent, Bool, e => Ef.keep.e(l, e), Ef.entry(l, map), Ef.Missing{}, none), pm.below(l, below))
  LA.pe.ladder_kept(map, l, k)
