# eukhe: the proof of LAW bind_press_plain

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

def Cvar.bind_press_plain(bs, k, as):
  LA.pv.expand_plain(1n+List.length(&2, Cv.Alias, as), Cv.bound(bs, k), as)
