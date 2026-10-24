# eukhe: the proof of LAW flight_ffi_reads
# The entry reads every input as the laws' reader does (LAE.ae.io);
# a whole request gets the leg after its step (LAE.ae.reply).

import Base
import ../../laws/auth_flight.bend as AuthFlight
import ./base/entry.bend as LAE

def AuthFlight.flight_ffi_reads(s, io, got):
  LAE.ae.ffi_reads(s, io, got)
