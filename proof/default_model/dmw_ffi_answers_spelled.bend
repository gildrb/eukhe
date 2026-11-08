# eukhe: the proof of LAW dmw_ffi_answers_spelled
#
# PROOF: the spelled request is the entry's encoding (LS.dms.req), which
# answers the encoded resolution (dmw_answers), the spelled resolution
# (LS.dms.res).

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../laws/default_model.bend as DefaultModel
import ./base/spell.bend as LS
import ./dmw_answers.bend as PDmwAnswers

def DefaultModel.dmw_ffi_answers_spelled(x, fits):
  %LS.dms.req(x, "") : {FDm.ffi(_) == DefaultModel.dmw_spell_answer(x) : String}
  Equal.trans(String, FDm.ffi(FDm.put_in(x, "")), FDm.put_res(Dm.resolve(x), ""), DefaultModel.dmw_spell_answer(x), DefaultModel.dmw_answers(x, fits), LS.dms.res(Dm.resolve(x), ""))
