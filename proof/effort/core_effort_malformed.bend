# eukhe: the proof of LAW core_effort_malformed

import Base
import ../../bend/ffi_effort.bend as FEf
import ../../bend/wire.bend as Wr
import ../../laws/effort.bend as Effort

def Effort.core_effort_malformed(s, h):
  %Equal.sym(Wr.Dec<FEf.Req>, FEf.get_req(s), Wr.Bad{}, h) : {FEf.ffi.go(_) == Wr.err("ladder request: malformed") : String}
  {==}
