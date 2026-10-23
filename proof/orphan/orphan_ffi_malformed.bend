# eukhe: the proof of LAW orphan_ffi_malformed

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan

def Orphan.orphan_ffi_malformed(s, h):
  %Equal.sym(Wr.Dec<FO.Req>, FO.get_req(s), Wr.Bad{}, h) : {FO.ffi.go(_) == Wr.err("orphan: malformed request") : String}
  {==}
