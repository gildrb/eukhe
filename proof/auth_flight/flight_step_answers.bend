# eukhe: the proof of LAW flight_step_answers
# Every event Rust writes reads back with nothing left (the wire's round
# trips, LAE.ae.get), so the entry steps F.desk.step on it and spells the
# answer as the laws' speller does (LAE.ae.put).

import Base
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def AuthFlightEntry.flight_step_answers(d, e, fits):
  LAE.ae.answers_code(d, e, fits)
