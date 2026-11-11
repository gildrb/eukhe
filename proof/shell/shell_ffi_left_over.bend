# eukhe: the proof of LAW shell_ffi_left_over
# The decoder reads the request back with the input after it (LASh.sh.rt); that input is not empty, so the request is not the whole input (wire_end_exact).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base.bend as LASh

def Shell.shell_ffi_left_over(q, more, fits, some):
  %Equal.sym(Wr.Dec<FSh.Req>, FSh.get_req(Shell.spell_req(q, more)), Wr.Got{q, more}, LASh.sh.rt(q, more, fits)) : {FSh.run(_) == Shell.malformed() : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {FSh.run.end(_, q) == Shell.malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {FSh.run.end(_, q) == Shell.malformed() : String}
  {==}
