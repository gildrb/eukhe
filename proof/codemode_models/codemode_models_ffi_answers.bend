# eukhe: the proof of LAW codemode_models_ffi_answers

import Base
import ../../bend/codemode_models.bend as Mod
import ../../bend/ffi_codemode_models.bend as FMod
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/codemode_models/entry.bend as CodemodeModelsEntry
import ../context_order/base.bend as LACo
import ./base/read.bend as LACmRead
import ./base/reply.bend as LACmReply

# PROOF of LAW codemode_models_ffi_answers: the entry reads the request back whole with nothing left (cmq.req) and answers the model's answer with encoders equal to the spec's spellers (cmy.answer).

def CodemodeModelsEntry.codemode_models_ffi_answers(q, h):
  %Equal.sym(Wr.Dec<FMod.Req>, FMod.get_req(CodemodeModelsEntry.spell_req(q, "")), Wr.Got{q, ""}, LACmRead.cmq.req(q, "", h)) : {FMod.ffi.got(_) == CodemodeModelsEntry.spell_reply(q) : String}
  LACmReply.cmy.answer(q)
