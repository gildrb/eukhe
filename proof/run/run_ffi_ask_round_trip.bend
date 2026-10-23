# eukhe: the proof of LAW run_ffi_ask_round_trip

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.run_ffi_ask_round_trip(a, rest, h):
  LA.rk.rt_ask(a, rest, h)
