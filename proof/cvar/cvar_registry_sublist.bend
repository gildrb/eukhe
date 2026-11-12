# eukhe: the proof of LAW cvar_registry_sublist
# The registry onto K is K, then some declarations of xs in order: declare
# keeps K or adds the declaration last (LW.wh.reg).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/whole.bend as CvarWhole
import ./base/whole.bend as LW

def CvarWhole.cvar_registry_sublist(xs):
  LW.wh.reg(xs, Nil{})
