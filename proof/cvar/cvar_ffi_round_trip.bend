# eukhe: the proof of LAW cvar_ffi_round_trip

import Base
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

def Cvar.cvar_ffi_round_trip(as, cs, rest, h):
  LA.pvf.xreq_rt(as, cs, rest, h)
