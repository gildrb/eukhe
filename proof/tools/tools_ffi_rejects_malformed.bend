# eukhe: the proof of LAW tools_ffi_rejects_malformed

import Base
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../bend/ffi_tools.bend as FTl
import ../../LAWS.bend as Laws

def Laws.tools_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<List<&2, Tl.Seg>>, FTl.get_req(s), Wr.Bad{}, bad) : {Laws.wire_opens_err(FTl.answer(_)) == True{} : Bool}
  {==}
