# eukhe: the proof of LAW cvar_ffi_round_trip

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.cvar_ffi_round_trip(as, cs, rest, h):
  LA.pvf.xreq_rt(as, cs, rest, h)
