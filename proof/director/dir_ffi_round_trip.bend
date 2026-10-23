# eukhe: the proof of LAW dir_ffi_round_trip

import Base
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_ffi_round_trip(q, rest, h):
  LA.pdf.req_rt(q, rest, h)
