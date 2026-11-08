# eukhe: the proof of LAW child_entry_answers_spelled
#
# PROOF: the spelled request reads back stage by stage to its last stage
# (LA.lo.run), which with nothing left answers the code's reply encoder on
# the model's decision, the spec's spelling of it (LA.lo.answer, LA.sp.*).

import Base
import ../../bend/ffi_child.bend as FCh
import ../../laws/child.bend as Child
import ./base.bend as LA

def Child.child_entry_answers_spelled(r, fits):
  Equal.trans(String, FCh.ffi(Child.ch_spell_req(r, "")), LA.lo.fin(r, True{}), Child.ch_spell_answer(r), LA.lo.run(r, "", fits), LA.lo.answer(r))
