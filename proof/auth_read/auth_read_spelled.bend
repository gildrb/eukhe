# eukhe: the proof of LAW auth_read_spelled
# Each decoder stage answers a value only for the spelling of what it read,
# within the wire (LAR.ar.x.*, from wire_nat_exact and
# wire_nat_decoded_fits); a verdict is answered only for a request read
# whole (LAR.ar.top).

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_read.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def AuthRead.auth_read_spelled(s, ok):
  LAR.ar.top(s, FR.get_query(Wr.get_nat(s)), LAR.ar.x.tag(s, Wr.get_nat(s), {==}), ok)
