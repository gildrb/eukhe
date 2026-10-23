# eukhe: the proof of LAW tools_ffi_rejects_left_over

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tools.bend as Tools

def Tools.tools_ffi_rejects_left_over(s, q, r, got, more):
  %Equal.sym(Wr.Dec<List<&2, Tl.Seg>>, FTl.get_req(s), Wr.Got{q, r}, got) : {LawsBase.wire_opens_err(FTl.answer(_)) == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(r), False{}, more) : {LawsBase.wire_opens_err(FTl.reply(_, q)) == True{} : Bool}
  {==}
