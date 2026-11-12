# eukhe: the proof of LAW restart_ffi_answers_spelled
# The entry's decoder reads the spelled request back with nothing after it
# (LAE.rse.rt); the entry then answers the model's decision, spelled as
# the laws spell it (LAE.rse.answer).

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise
import ./base/entry.bend as LAE

def Supervise.restart_ffi_answers_spelled(q, fits):
  %Equal.sym(Wr.Dec<FS.Req>, FS.get_req(Supervise.rs_spell_req(q, "")), Wr.Got{q, ""}, LAE.rse.rt(q, "", fits)) : {FS.ffi.go(_) == Supervise.rs_spell_answer(q) : String}
  LAE.rse.answer(q)
