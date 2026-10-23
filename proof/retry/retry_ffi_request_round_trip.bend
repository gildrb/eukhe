# eukhe: the proof of LAW retry_ffi_request_round_trip

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

# The entry
# ---------

def Laws.retry_ffi_request_round_trip(q, rest, h):
  LA.rw.req_rt(q, rest, h)
