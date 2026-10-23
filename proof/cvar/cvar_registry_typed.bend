# eukhe: the proof of LAW cvar_registry_typed

import Base
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

def Cvar.cvar_registry_typed(xs):
  LA.pv.cvar_registry_typed(xs)
