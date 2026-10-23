# eukhe: the proof of LAW tiny_ffi_rejects_left_over

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny.bend as Tiny

def Tiny.tiny_ffi_rejects_left_over(s, q, r, got, more):
  %Equal.sym(Wr.Dec<FTn.Req>, FTn.get_req(s), Wr.Got{q, r}, got) : {LawsBase.wire_opens_err(FTn.answer(_)) == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(r), False{}, more) : {LawsBase.wire_opens_err(FTn.reply(_, q)) == True{} : Bool}
  {==}
