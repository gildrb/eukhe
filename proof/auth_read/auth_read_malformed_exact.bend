# eukhe: the proof of LAW auth_read_malformed_exact
# The entry reads every input as the laws' reader does; where that
# reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_auth_read.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def AuthRead.auth_read_malformed_exact(s, no):
  %LAR.ar.go(Wr.get_nat(s)) : {FR.ffi.go(_) == SCon{'E', SCon{' ', "auth_read: malformed request"}} : String}
  LAR.ar.ffi_bad(AuthRead.ar_read.go(Wr.get_nat(s)), no)
