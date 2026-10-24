# eukhe: the proof of LAW flight_step_reads
# The entry reads every input as the laws' reader does (LAE.ae.ev);
# its book is the laws' book (LAE.ae.book), its reply the laws' spelling.

import Base
import ../../laws/auth_flight.bend as AuthFlight
import ./base/entry.bend as LAE

def AuthFlight.flight_step_reads(b, s, e, got):
  LAE.ae.step_reads(b, s, e, got)
