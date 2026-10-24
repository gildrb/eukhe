# eukhe: the proof of LAW shell_ffi_answers
# The entry answers as the laws spell (LASh.sh.exact), and the reader reads back the request Rust writes (LASh.sh.rt).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def Shell.shell_ffi_answers(q, fits):
  %Equal.sym(String, FSh.ffi(Shell.spell_req(q, "")), Shell.spec(Shell.spell_req(q, "")), LASh.sh.exact(Shell.spell_req(q, ""))) : {_ == Shell.spell_answer(q) : String}
  %Equal.sym(Wr.Dec<FSh.Req>, Shell.read_req(Shell.spell_req(q, "")), Wr.Got{q, ""}, LASh.sh.rt(q, "", fits)) : {Shell.spec.run(_) == Shell.spell_answer(q) : String}
  {==}
