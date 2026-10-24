# eukhe: the proof of LAW flight_ffi_answers
# Every request Rust writes reads back (the wire's round trips,
# LAE.read_io_spell); a whole request gets the leg after its step.

import Base
import ../../laws/auth_flight.bend as AuthFlight
import ./base/entry.bend as LAE

def AuthFlight.flight_ffi_answers(io, fits):
  LAE.ae.ffi_reads(AuthFlight.af_spell_io(io), io, LAE.ae.read_io_spell(io, fits))
