# eukhe: the proof of LAW flight_step_answers
# Every event Rust writes reads back (the wire's round trips,
# LAE.read_ev_spell); a whole event gets the book's answer.

import Base
import ../../laws/auth_flight.bend as AuthFlight
import ./base/entry.bend as LAE

def AuthFlight.flight_step_answers(b, e, fits):
  LAE.ae.step_reads(b, AuthFlight.af_spell_ev(e), e, LAE.ae.read_ev_spell(e, fits))
