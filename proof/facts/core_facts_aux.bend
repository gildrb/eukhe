# eukhe: the proof of LAW core_facts_aux

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ./base.bend as LA

def Facts.core_facts_aux(c, d, a, top, h):
  %LA.pc.f_req(FFx.Aux{c, d, a, top}, "", h) : {FFx.ffi.go(_) == Wr.put_nat(Fx.aux(c, d, a, top), "") : String}
  {==}
