# eukhe: the proof of LAW orphan_ffi_left_over

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_orphan.bend as FO
import ../../LAWS.bend as Laws

def Laws.orphan_ffi_left_over(s, q, r, h, ne):
  %Equal.sym(Wr.Dec<FO.Req>, FO.get_req(s), Wr.Got{q, r}, h) : {FO.ffi.go(_) == Wr.err("orphan: input left over") : String}
  %Equal.sym(Bool, String.is_empty(r), False{}, ne) : {FO.ffi.fin(_, q) == Wr.err("orphan: input left over") : String}
  {==}
