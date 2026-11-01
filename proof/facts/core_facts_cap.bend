# eukhe: the proof of LAW core_facts_cap

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../laws/facts.bend as Facts
import ./base.bend as LA

def Facts.core_facts_cap(x, mm, n, w, h):
  %LA.pc.f_req(FFx.Cap{x, mm, n, w}, "", h) : {FFx.ffi.go(_) == FFx.put_mnat(Fx.cap(x, mm, n, w), "") : String}
  {==}
