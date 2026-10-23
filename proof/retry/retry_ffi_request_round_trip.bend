# eukhe: the proof of LAW retry_ffi_request_round_trip

import Base
import ../../laws/retry.bend as Retry
import ./base.bend as LA

# The entry
# ---------

def Retry.retry_ffi_request_round_trip(q, rest, h):
  LA.rw.req_rt(q, rest, h)
