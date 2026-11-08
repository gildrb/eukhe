# eukhe: the proof of LAW core_facts_answers_spelled
#
# PROOF: the grammar's spelling is the entry's writer (LA.fs.req), whose
# request reads back whole (LA.pc.f_req); nothing is left, so the entry
# answers, and its answer is the spelled reply (LA.fs.answer).

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def fas.main(+q: FFx.Req, fits: {Facts.core_facts_req_fits(q) == True{} : Bool}) -> {FFx.ffi(Facts.facts_spell_req(q, "")) == Facts.facts_spell_answer(q) : String}:
  Equal.trans(String, FFx.ffi(Facts.facts_spell_req(q, "")), FFx.answer(q), Facts.facts_spell_answer(q), LA.fs.run(q, "", fits), LA.fs.answer(q))

def Facts.core_facts_answers_spelled(q, fits):
  fas.main(q, fits)
