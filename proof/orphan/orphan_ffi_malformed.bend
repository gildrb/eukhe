# eukhe: the proof of LAW orphan_ffi_malformed

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_orphan.bend as FO
import ../../LAWS.bend as Laws

def Laws.orphan_ffi_malformed(s, h):
  %Equal.sym(Wr.Dec<FO.Req>, FO.get_req(s), Wr.Bad{}, h) : {FO.ffi.go(_) == Wr.err("orphan: malformed request") : String}
  {==}
