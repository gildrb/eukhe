# eukhe: the proof of LAW core_effort_cycle

import Base
import ../../bend/effort.bend as Ef
import ../../bend/ffi_effort.bend as FEf
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def Effort.core_effort_cycle(f, l, d, h):
  match f:
    case FEf.Facts{+flag, +by_map, +explicit, +rule, +reasoning, +plain}:
      %LA.pc.e_req(FEf.Cycle{FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}, l, d}, "", h) : {FEf.ffi.go(_) == FEf.put_mlv(Ef.cycle(Effort.core_effort_model(FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}), l, d), "") : String}
      {==}
