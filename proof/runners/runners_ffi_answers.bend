# eukhe: the proof of LAW runners_ffi_answers
# The entry answers as the laws spell; the reader reads back the request
# Rust writes.

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/runners.bend as Runners
import ./base/entry.bend as LARn

def Runners.runners_ffi_answers(q, fits):
  %Equal.sym(String, FRu.ffi(Runners.spell_req(q, "")), Runners.spec(Runners.spell_req(q, "")), LARn.rn.exact(Runners.spell_req(q, ""))) : {_ == Runners.spell_answer(q) : String}
  %Equal.sym(Wr.Dec<FRu.Req>, Runners.read_req(Runners.spell_req(q, "")), Wr.Got{q, ""}, LARn.rn.rt(q, "", fits)) : {Runners.spec.run(_) == Runners.spell_answer(q) : String}
  {==}
