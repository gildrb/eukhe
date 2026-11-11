# eukhe: the proof of LAW flight_step_reads
# The entry reads the event as the laws' reader does (LAE.ae.ev); a whole
# event steps the desk as the laws' desk.

import Base
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def AuthFlightEntry.flight_step_reads(d, s, e, got):
  LAE.ae.step_reads(d, s, e, got)
