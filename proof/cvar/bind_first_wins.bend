# eukhe: the proof of LAW bind_first_wins

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

def Cvar.bind_first_wins(k, c, rest, as):
  %LA.cvar.pv.eq_refl(k) : {Cv.expand(Cv.bound.go(Cv.KeyBind{k, c} <> rest, k, _), as) == Cv.expand(c, as) : Cv.Exp}
  {==}
