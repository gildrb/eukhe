# eukhe: the proof of LAW flight_step_malformed_exact
# The entry reads the input as the laws' reader does (LAE.ae.ev); every
# reading that is not exactly one event keeps the desk and answers the
# error form.

import Base
import ../../bend/ffi_auth_flight.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def AuthFlightEntry.flight_step_malformed_exact(d, s, no):
  %LAE.ae.ev(Wr.get_nat(s)) : {FA.step.go(d, _) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}
  LAE.ae.step_bad(AuthFlightEntry.af_read_ev.go(Wr.get_nat(s)), d, no)
