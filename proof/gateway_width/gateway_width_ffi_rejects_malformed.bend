# eukhe: the proof of LAW gateway_width_ffi_rejects_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_gateway_width.bend as FGw
import ../../LAWS.bend as Laws

def Laws.gateway_width_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<List<&2, List<&2, Nat>>>, FGw.get_req(s), Wr.Bad{}, bad) : {Laws.wire_opens_err(FGw.answer(_)) == True{} : Bool}
  {==}
