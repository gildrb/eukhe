# eukhe: the proof of LAW core_infer_malformed

import Base
import ../../bend/ffi_infer.bend as FIn
import ../../bend/wire.bend as Wr
import ../../laws/infer.bend as Infer

def Infer.core_infer_malformed(s, h):
  %Equal.sym(Wr.Dec<FIn.Req>, FIn.get_req(s), Wr.Bad{}, h) : {FIn.ffi.go(_) == Wr.err("strict plan request: malformed") : String}
  {==}
