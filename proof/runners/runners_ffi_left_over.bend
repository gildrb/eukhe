# eukhe: the proof of LAW runners_ffi_left_over
# The entry's reader reads the request back with the input after it
# (rn.rt); that input is not empty, so the request is not the whole input
# (wire_end_exact).

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/runners.bend as Runners
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base/entry.bend as LARn

def Runners.runners_ffi_left_over(q, more, fits, some):
  %Equal.sym(Wr.Dec<FRu.Req>, FRu.get_req(Runners.spell_req(q, more)), Wr.Got{q, more}, LARn.rn.rt(q, more, fits)) : {FRu.run(_) == Runners.malformed() : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {FRu.run.end(_, q) == Runners.malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {FRu.run.end(_, q) == Runners.malformed() : String}
  {==}
