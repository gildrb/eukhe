# eukhe: the proof of LAW flight_ffi_malformed_exact
# The entry reads every input as the laws' reader does; where that
# reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_auth_flight.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/auth_flight.bend as AuthFlight
import ./base/entry.bend as LAE

def AuthFlight.flight_ffi_malformed_exact(s, no):
  %LAE.ae.io(Wr.get_nat(s)) : {FA.ffi.go(_) == SCon{'E', SCon{' ', "auth_flight: malformed request"}} : String}
  LAE.ae.ffi_bad(AuthFlight.af_read_io.go(Wr.get_nat(s)), no)
