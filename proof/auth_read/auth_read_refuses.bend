# eukhe: the proof of LAW auth_read_refuses
# The entry answers a verdict, which never opens with 'E'
# (LAR.ar.verdict_ok), or its one error form (LAR.ar.refuse).

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_read.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def AuthRead.auth_read_refuses(s, bad):
  LAR.ar.refuse(FR.get_query(Wr.get_nat(s)), bad)
