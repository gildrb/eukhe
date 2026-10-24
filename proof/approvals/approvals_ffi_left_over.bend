# eukhe: the proof of LAW approvals_ffi_left_over
# The reader reads the request back with the input after it; that input
# is not empty, so the request is not the whole input (wire_end_exact).

import Base
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../../laws/approvals.bend as Approvals
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base/entry.bend as LAAp

def Approvals.approvals_ffi_left_over(q, more, fits, some):
  %Equal.sym(String, FAm.ffi(Approvals.spell_req(q, more)), Approvals.spec(Approvals.spell_req(q, more)), LAAp.ap.exact(Approvals.spell_req(q, more))) : {_ == Approvals.malformed() : String}
  %Equal.sym(Wr.Dec<FAm.Req>, Approvals.read_req(Approvals.spell_req(q, more)), Wr.Got{q, more}, LAAp.ap.rt(q, more, fits)) : {Approvals.spec.run(_) == Approvals.malformed() : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {Approvals.spec.end(_, q) == Approvals.malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {Approvals.spec.end(_, q) == Approvals.malformed() : String}
  {==}
