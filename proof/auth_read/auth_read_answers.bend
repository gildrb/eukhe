# eukhe: the proof of LAW auth_read_answers
# Every request Rust writes reads back through the entry's decoder
# (LAR.ar.spell_go); the entry answers the verdict the laws spell (LAR.ar.reply).

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_read.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def AuthRead.auth_read_answers(a, now, r, fnow, fr):
  LAR.ar.answers_fwd(a, now, r, fnow, fr)
