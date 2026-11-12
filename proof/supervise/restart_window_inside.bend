# eukhe: the proof of LAW restart_window_inside
# The one age, g ms older, is tested against the window; the premise says
# it is inside, so it is kept behind the new failure.

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise

def Supervise.restart_window_inside(c, a, g, inside):
  %Equal.sym(Bool, Nat.is_lt(Nat.add(g, a), Su.Cfg.w(c)), True{}, inside) : {0n <> Su.keep.put(_, Nat.add(g, a), Nil{}) == [0n, Nat.add(g, a)] : List<&2, Nat>}
  {==}
