# eukhe: the proof of LAW auth_read_left_over
# The request with input after it reads back with that input left
# (LAR.ar.spell_app, LAR.ar.spell_go); input left is refused.

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_read.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def AuthRead.auth_read_left_over(a, now, r, c, t, fnow, fr):
  LAR.ar.left_over(a, now, r, c, t, fnow, fr)
