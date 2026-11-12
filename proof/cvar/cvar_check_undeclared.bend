# eukhe: the proof of LAW cvar_check_undeclared
# Case by case on the declaration and the layer (LV.ck.undeclared_at).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/verdict.bend as LV

def Cvar.cvar_check_undeclared(ds, l, s):
  match s:
    case Cv.Bind{+i, +v}:
      LV.ck.undeclared_at(Cv.find(ds, i), l, i, v)
