# eukhe: the proof of LAW tiny_ffi_rejects_malformed

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny.bend as Tiny

def Tiny.tiny_ffi_rejects_malformed(s, bad):
  %Equal.sym(Wr.Dec<FTn.Req>, FTn.get_req(s), Wr.Bad{}, bad) : {LawsBase.wire_opens_err(FTn.answer(_)) == True{} : Bool}
  {==}
