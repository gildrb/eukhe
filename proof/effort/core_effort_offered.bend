# eukhe: the proof of LAW core_effort_offered

import Base
import ../../bend/effort.bend as Ef
import ../../bend/ffi_effort.bend as FEf
import ../../bend/wire.bend as Wr
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def Effort.core_effort_offered(f, h):
  match f:
    case FEf.Facts{+flag, +by_map, +explicit, +rule, +reasoning, +plain}:
      %LA.pc.e_req(FEf.Offered{FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}}, "", h) : {FEf.ffi.go(_) == Wr.put_list(~Ef.Lv, ~FEf.put_lv, Ef.offered(Effort.core_effort_model(FEf.Facts{flag, by_map, explicit, rule, reasoning, plain})), "") : String}
      {==}
