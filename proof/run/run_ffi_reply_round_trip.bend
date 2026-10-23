# eukhe: the proof of LAW run_ffi_reply_round_trip

import Base
import ../../laws/run.bend as Run
import ./base.bend as LA

def Run.run_ffi_reply_round_trip(x, rest):
  LA.rk.rt_reply(x, rest)
