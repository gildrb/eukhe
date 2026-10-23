# eukhe: the proof of LAW bind_unbound_runs_nothing

import Base
import ../../bend/cvar.bend as Cv
import ../../LAWS.bend as Laws

def Laws.bind_unbound_runs_nothing(bs, k, as, free):
  %Equal.sym(List<&2, Cv.Cmd>, Cv.bound(bs, k), Nil{}, free) : {Cv.expand(_, as) == Cv.Flat{Nil{}} : Cv.Exp}
  {==}
