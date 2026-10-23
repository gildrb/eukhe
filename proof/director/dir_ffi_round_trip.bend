# eukhe: the proof of LAW dir_ffi_round_trip

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.dir_ffi_round_trip(q, rest, h):
  LA.pdf.req_rt(q, rest, h)
