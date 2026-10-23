# eukhe: the proof of LAW core_facts_level

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ./base.bend as LA

def Facts.core_facts_level(l, c, d, h):
  %LA.pc.f_req(FFx.Level{l, c, d}, "", h) : {FFx.ffi.go(_) == Wr.put_nat(Fx.budget(c, d, Fx.Lv.of(l)), "") : String}
  {==}
