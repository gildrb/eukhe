# eukhe: the proof of LAW core_facts_room

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ./base.bend as LA

def Facts.core_facts_room(b, m, a, h):
  %LA.pc.f_req(FFx.Room{b, m, a}, "", h) : {FFx.ffi.go(_) == Wr.put_nat(Fx.room(b, m, a), "") : String}
  {==}
