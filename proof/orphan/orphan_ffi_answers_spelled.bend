# eukhe: the proof of LAW orphan_ffi_answers_spelled
#
# PROOF: the spelled request reads back field by field (LA.oe.run), which
# with nothing left answers the entry's reply on the model's decision, the
# spelled spec decision (LA.oe.answer).

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../laws/orphan.bend as Orphan
import ./base.bend as LA

def Orphan.orphan_ffi_answers_spelled(q, fits):
  Equal.trans(String, FO.ffi(Orphan.orphan_spell_req(q, "")), FO.put_reply(FO.decide(q), ""), Orphan.orphan_spell_answer(q), LA.oe.run(q, "", fits), LA.oe.answer(q))
