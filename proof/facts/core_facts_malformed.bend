# eukhe: the proof of LAW core_facts_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_facts.bend as FFx
import ../../LAWS.bend as Laws

def Laws.core_facts_malformed(s, h):
  %Equal.sym(Wr.Dec<FFx.Req>, FFx.get_req(s), Wr.Bad{}, h) : {FFx.ffi.go(_) == Wr.err("budget request: malformed") : String}
  {==}
