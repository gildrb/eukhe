# eukhe: the proof of LAW core_infer_answers_spelled
#
# PROOF: the spelled request is the entry's encoding (IS.is.req), which
# reads back whole (round trip), so with nothing left the entry answers
# its reply, the spelled reply of the model's plan (IS.is.answer).

import Base
import ../../bend/ffi_infer.bend as FIn
import ../../laws/infer.bend as Infer
import ./core_infer_answers_spelled/spell.bend as IS

def Infer.core_infer_answers_spelled(q, fits):
  Equal.trans(String, FIn.ffi(Infer.core_infer_spell_req(q, "")), FIn.answer(q), Infer.core_infer_spell_answer(q), IS.is.run(q, "", fits), IS.is.answer(q))
