# eukhe: the proof of LAW restart_ffi_left_over

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_supervise.bend as FS
import ../../LAWS.bend as Laws

def Laws.restart_ffi_left_over(s, q, r, h, ne):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(s), Wr.Got{q, r}, h) : {FS.ffi.go(_) == Wr.err("supervise: input left over") : String}
  %Equal.sym(Bool, String.is_empty(r), False{}, ne) : {FS.ffi.fin(_, q) == Wr.err("supervise: input left over") : String}
  {==}
