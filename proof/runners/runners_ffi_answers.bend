# eukhe: the proof of LAW runners_ffi_answers
# The entry's reader reads back the request Rust writes with nothing left
# (rn.rt), and the entry spells the model's decision as the laws do
# (rn.reply).

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/runners.bend as Runners
import ./base/entry.bend as LARn

def Runners.runners_ffi_answers(q, fits):
  %Equal.sym(Wr.Dec<FRu.Req>, FRu.get_req(Runners.spell_req(q, "")), Wr.Got{q, ""}, LARn.rn.rt(q, "", fits)) : {FRu.run(_) == Runners.spell_answer(q) : String}
  LARn.rn.reply(q)
