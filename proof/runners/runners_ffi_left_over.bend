# eukhe: the proof of LAW runners_ffi_left_over
# The reader reads the request back with the input after it; that input
# is not empty, so the request is not the whole input (wire_end_exact).

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/runners.bend as Runners
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base/entry.bend as LARn

def Runners.runners_ffi_left_over(q, more, fits, some):
  %Equal.sym(String, FRu.ffi(Runners.spell_req(q, more)), Runners.spec(Runners.spell_req(q, more)), LARn.rn.exact(Runners.spell_req(q, more))) : {_ == Runners.malformed() : String}
  %Equal.sym(Wr.Dec<FRu.Req>, Runners.read_req(Runners.spell_req(q, more)), Wr.Got{q, more}, LARn.rn.rt(q, more, fits)) : {Runners.spec.run(_) == Runners.malformed() : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {Runners.spec.end(_, q) == Runners.malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {Runners.spec.end(_, q) == Runners.malformed() : String}
  {==}
