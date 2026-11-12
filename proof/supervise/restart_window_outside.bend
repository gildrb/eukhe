# eukhe: the proof of LAW restart_window_outside
# The one age, g ms older, is tested against the window; the premise says
# it reached it, so only the new failure stays.

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise

def Supervise.restart_window_outside(c, a, g, outside):
  %Equal.sym(Bool, Nat.is_lt(Nat.add(g, a), Su.Cfg.w(c)), False{}, outside) : {0n <> Su.keep.put(_, Nat.add(g, a), Nil{}) == [0n] : List<&2, Nat>}
  {==}
