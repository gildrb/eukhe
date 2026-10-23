# eukhe: the proof of LAW core_facts_adjust

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.core_facts_adjust(base, mm, l, c, d, a, h):
  %LA.pc.f_req(FFx.Adjust{base, mm, l, c, d, a}, "", h) : {FFx.ffi.go(_) == FFx.put_fit(Fx.adjust(base, mm, l, c, d, a), "") : String}
  {==}
