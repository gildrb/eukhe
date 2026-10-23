# eukhe: the proof of LAW cvar_registry_typed

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.cvar_registry_typed(xs):
  LA.pv.cvar_registry_typed(xs)
