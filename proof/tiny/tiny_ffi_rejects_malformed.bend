# eukhe: the proof of LAW tiny_ffi_rejects_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_tiny.bend as FTn
import ../../LAWS.bend as Laws

def Laws.tiny_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<FTn.Req>, FTn.get_req(s), Wr.Bad{}, bad) : {Laws.wire_opens_err(FTn.answer(_)) == True{} : Bool}
  {==}
