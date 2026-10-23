# eukhe: the proof of LAW core_facts_left_over

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_facts.bend as FFx
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.core_facts_left_over(q, c, rest, h):
  %LA.pc.f_req(q, SCon{c, rest}, h) : {FFx.ffi.go(_) == Wr.err("budget request: input left over") : String}
  {==}
