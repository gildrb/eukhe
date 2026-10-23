# eukhe: the proof of LAW core_effort_clamp

import Base
import ../../bend/effort.bend as Ef
import ../../bend/ffi_effort.bend as FEf
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.core_effort_clamp(f, l, h):
  match f:
    case FEf.Facts{+flag, +by_map, +explicit, +rule, +reasoning, +plain}:
      %LA.pc.e_req(FEf.Clamp{FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}, l}, "", h) : {FEf.ffi.go(_) == FEf.put_lv(Ef.clamp(Laws.core_effort_model(FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}), l), "") : String}
      {==}
