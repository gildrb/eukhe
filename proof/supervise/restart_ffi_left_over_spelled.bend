# eukhe: the proof of LAW restart_ffi_left_over_spelled
# The reader reads the request back with the input after it; that input
# is not empty, so the request is not the whole input (wire_end_exact).

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base/entry.bend as LAE

def Supervise.restart_ffi_left_over_spelled(q, more, fits, some):
  %Equal.sym(String, FS.ffi(Supervise.rs_spell_req(q, more)), Supervise.rs_spec(Supervise.rs_spell_req(q, more)), LAE.rse.exact(Supervise.rs_spell_req(q, more))) : {_ == Supervise.rs_left_over() : String}
  %Equal.sym(Wr.Dec<FS.Req>, Supervise.rs_read_req(Supervise.rs_spell_req(q, more)), Wr.Got{q, more}, LAE.rse.rt(q, more, fits)) : {Supervise.rs_spec.run(_) == Supervise.rs_left_over() : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {Supervise.rs_spec.end(_, q) == Supervise.rs_left_over() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {Supervise.rs_spec.end(_, q) == Supervise.rs_left_over() : String}
  {==}
