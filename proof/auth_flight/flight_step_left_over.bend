# eukhe: the proof of LAW flight_step_left_over
# The spelled event reads back with the extra input as its rest
# (LAE.ae.step_spelled); a rest that is not empty ends in the
# malformed-event error form with the desk kept.

import Base
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def AuthFlightEntry.flight_step_left_over(d, e, fits, c, t):
  LAE.ae.step_spelled(d, e, SCon{c, t}, fits)
