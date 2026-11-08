# eukhe: the proof of LAW wfw_answers_spelled
#
# PROOF: the laws' spelling of the request is the entry's encoding, which
# reads back whole (sp.ffi); with nothing left the entry answers the
# model's answer encoded, the laws' spelled reply (sp.answer).

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../laws/workflow/model.bend as Workflow
import ./wfw_answers_spelled/spell.bend as SP

def Workflow.wfw_answers_spelled(q, fits):
  Equal.trans(String, FW.ffi(Workflow.wfw_spell_req(q, "")), FW.answer(q), Workflow.wfw_spell_answer(q), SP.sp.ffi(q, "", fits), SP.sp.answer(q))
