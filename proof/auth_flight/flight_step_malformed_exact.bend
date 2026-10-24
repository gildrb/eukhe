# eukhe: the proof of LAW flight_step_malformed_exact
# The entry reads every input as the laws' reader does; where that
# reader finds no whole event, the book stays and the entry answers its
# error form.

import Base
import ../../bend/ffi_auth_flight.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/auth_flight.bend as AuthFlight
import ./base/entry.bend as LAE

def AuthFlight.flight_step_malformed_exact(b, s, no):
  %LAE.ae.ev(Wr.get_nat(s)) : {FA.step.go(b, _) == (FA.Open{b}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}
  LAE.ae.step_bad(AuthFlight.af_read_ev.go(Wr.get_nat(s)), b, no)
