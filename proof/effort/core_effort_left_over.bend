# eukhe: the proof of LAW core_effort_left_over

import Base
import ../../bend/ffi_effort.bend as FEf
import ../../bend/wire.bend as Wr
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def Effort.core_effort_left_over(q, c, rest, h):
  %LA.pc.e_req(q, SCon{c, rest}, h) : {FEf.ffi.go(_) == Wr.err("ladder request: input left over") : String}
  {==}
