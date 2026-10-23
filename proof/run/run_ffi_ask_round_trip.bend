# eukhe: the proof of LAW run_ffi_ask_round_trip

import Base
import ../../laws/run.bend as Run
import ./base.bend as LA

def Run.run_ffi_ask_round_trip(a, rest, h):
  LA.rk.rt_ask(a, rest, h)
