# eukhe: the proof of LAW core_effort_answers_spelled
#
# PROOF: the spelled request is the entry's encoding (ES.es.req), which
# reads back whole (round trip), so with nothing left the entry answers
# its reply, the spelled reply of the model's decision (ES.es.answer).

import Base
import ../../bend/ffi_effort.bend as FEf
import ../../laws/effort/ladder.bend as EffortLadder
import ./core_effort_answers_spelled/spell.bend as ES

def EffortLadder.core_effort_answers_spelled(q, fits):
  Equal.trans(String, FEf.ffi(EffortLadder.core_effort_spell_req(q, "")), FEf.answer(q), EffortLadder.core_effort_spell_answer(q), ES.es.run(q, "", fits), ES.es.answer(q))
