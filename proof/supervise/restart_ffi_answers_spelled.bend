# eukhe: the proof of LAW restart_ffi_answers_spelled
# The entry answers as the laws spell; the reader reads back the request
# Rust writes.

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise
import ./base/entry.bend as LAE

def Supervise.restart_ffi_answers_spelled(q, fits):
  %Equal.sym(String, FS.ffi(Supervise.rs_spell_req(q, "")), Supervise.rs_spec(Supervise.rs_spell_req(q, "")), LAE.rse.exact(Supervise.rs_spell_req(q, ""))) : {_ == Supervise.rs_spell_answer(q) : String}
  %Equal.sym(Wr.Dec<FS.Req>, Supervise.rs_read_req(Supervise.rs_spell_req(q, "")), Wr.Got{q, ""}, LAE.rse.rt(q, "", fits)) : {Supervise.rs_spec.run(_) == Supervise.rs_spell_answer(q) : String}
  {==}
