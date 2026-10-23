# eukhe: the proof of LAW env_ffi_round_trip

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.env_ffi_round_trip(q, rest, h):
  LA.pce.req_rt(q, rest, h)
