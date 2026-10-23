# eukhe: the proof of LAW tools_ffi_rejects_malformed

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tools.bend as Tools

def Tools.tools_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<List<&2, Tl.Seg>>, FTl.get_req(s), Wr.Bad{}, bad) : {LawsBase.wire_opens_err(FTl.answer(_)) == True{} : Bool}
  {==}
