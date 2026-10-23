# eukhe: the proof of LAW env_ffi_round_trip

import Base
import ../../laws/child_env.bend as ChildEnv
import ./base.bend as LA

def ChildEnv.env_ffi_round_trip(q, rest, h):
  LA.pce.req_rt(q, rest, h)
