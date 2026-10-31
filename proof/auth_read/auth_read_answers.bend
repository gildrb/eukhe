# eukhe: the proof of LAW auth_read_answers
# Every request Rust writes reads back (LAR.ar.read_spell); a whole
# request gets the verdict on it (LAR.ar.ffi_reads).

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def AuthRead.auth_read_answers(a, now, r, fnow, fr):
  LAR.ar.ffi_reads(AuthRead.ar_spell(a, now, r), F.Query{a, now, r}, LAR.ar.read_spell(a, now, r, fnow, fr))
