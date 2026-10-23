# eukhe: the proof of LAW restart_ffi_left_over

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise

def Supervise.restart_ffi_left_over(s, q, r, h, ne):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(s), Wr.Got{q, r}, h) : {FS.ffi.go(_) == Wr.err("supervise: input left over") : String}
  %Equal.sym(Bool, String.is_empty(r), False{}, ne) : {FS.ffi.fin(_, q) == Wr.err("supervise: input left over") : String}
  {==}
