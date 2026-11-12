# eukhe: the proof of LAW shell_ffi_answers
# The entry's decoder reads back the request Rust writes (LASh.sh.rt), and its reply encoder is the laws' spell_answer (LASh.sh.reply).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def Shell.shell_ffi_answers(q, fits):
  %Equal.sym(Wr.Dec<FSh.Req>, FSh.get_req(Shell.spell_req(q, "")), Wr.Got{q, ""}, LASh.sh.rt(q, "", fits)) : {FSh.run(_) == Shell.spell_answer(q) : String}
  LASh.sh.reply(q)
