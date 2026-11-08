# eukhe: the proof of LAW afw_answers_spelled
#
# PROOF: the grammar's spelling is the entry's own encoding (LA.pfs.req),
# which reads back (afw_req_round_trip); with nothing left the entry
# answers the model's decision, encoded, which is the spelled spec
# decision (LA.pfs.answer).

import Base
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../laws/aux_fallback/wire.bend as AuxFallbackWire
import ./base.bend as LA

def AuxFallbackWire.afw_answers_spelled(x, fits):
  Equal.trans(String, FAf.ffi(AuxFallbackWire.afw_spell_req(x, "")), FAf.answer(x), AuxFallbackWire.afw_spell_answer(x), LA.pfs.run(x, "", fits), LA.pfs.answer(x))
