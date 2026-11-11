# eukhe: the proof of LAW restart_ffi_answers_spelled
# The entry's reader reads back the request Rust writes (LAE.rse.rt),
# nothing is left, and the entry answers as the laws spell the model's
# decision (LAE.rse.answer).

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise
import ./base/entry.bend as LAE

def Supervise.restart_ffi_answers_spelled(q, fits):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(Supervise.rs_spell_req(q, "")), Wr.Got{q, ""}, LAE.rse.rt(q, "", fits)) : {FS.ffi.go(_) == Supervise.rs_spell_answer(q) : String}
  LAE.rse.answer(q)
