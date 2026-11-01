# eukhe: the proof of LAW flight_step_answers
# Every event Rust writes reads back (the wire's round trips,
# LAE.ae.read_ev_spell); a whole event steps the desk as the laws' desk
# (LAE.ae.step_reads, over LAE.ae.desk).

import Base
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def AuthFlightEntry.flight_step_answers(d, e, fits):
  LAE.ae.answers(d, e, fits)
