# eukhe: the proof of LAW run_ffi_reply_round_trip

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.run_ffi_reply_round_trip(x, rest):
  LA.rk.rt_reply(x, rest)
