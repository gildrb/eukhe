# eukhe: the proof of LAW cvar_check_global
# Case by case on the declaration and the layer (LV.ck.global_at).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/verdict.bend as LV

def Cvar.cvar_check_global(ds, l, s):
  match s:
    case Cv.Bind{+i, +v}:
      LV.ck.global_at(Cv.find(ds, i), l, i, v)
