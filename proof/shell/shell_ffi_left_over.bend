# eukhe: the proof of LAW shell_ffi_left_over
# The reader reads the request back with the input after it (LASh.sh.rt); that input is not empty, so the request is not the whole input (wire_end_exact).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ../../laws/wire.bend as Wire
import ../wire/wire_end_exact.bend as PWireEndExact
import ./base.bend as LASh

def Shell.shell_ffi_left_over(q, more, fits, some):
  %Equal.sym(String, FSh.ffi(Shell.spell_req(q, more)), Shell.spec(Shell.spell_req(q, more)), LASh.sh.exact(Shell.spell_req(q, more))) : {_ == Shell.malformed() : String}
  %Equal.sym(Wr.Dec<FSh.Req>, Shell.read_req(Shell.spell_req(q, more)), Wr.Got{q, more}, LASh.sh.rt(q, more, fits)) : {Shell.spec.run(_) == Shell.malformed() : String}
  %Equal.sym(Bool, Wr.end(more), String.is_empty(more), Wire.wire_end_exact(more)) : {Shell.spec.end(_, q) == Shell.malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {Shell.spec.end(_, q) == Shell.malformed() : String}
  {==}
