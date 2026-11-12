# eukhe: the proof of LAW restart_ffi_left_over_spelled
# The entry's decoder reads the request back with the input after it; that
# input is not empty, so the request is not the whole input (Wr.end is String.is_empty).

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise
import ./base/entry.bend as LAE

def Supervise.restart_ffi_left_over_spelled(q, more, fits, some):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(Supervise.rs_spell_req(q, more)), Wr.Got{q, more}, LAE.rse.rt(q, more, fits)) : {FS.ffi.go(_) == Supervise.rs_left_over() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {FS.ffi.fin(_, q) == Supervise.rs_left_over() : String}
  {==}
