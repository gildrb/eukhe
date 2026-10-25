# eukhe: the proof of LAW codemode_describe_ffi_answers

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../bend/ffi_codemode_describe.bend as FDsc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/codemode_describe.bend as CodemodeDescribe
import ./base/read.bend as LACdRead
import ./base/reply.bend as LACdReply

# PROOF of LAW codemode_describe_ffi_answers: the entry reads the request back whole with nothing left (cdq.req) and answers the model's answer with encoders equal to the spec's spellers (cdy.answer).

def CodemodeDescribe.codemode_describe_ffi_answers(q, h):
  %Equal.sym(Wr.Dec<FDsc.Req>, FDsc.get_req(CodemodeDescribe.spell_req(q, "")), Wr.Got{q, ""}, LACdRead.cdq.req(q, "", h)) : {FDsc.ffi.got(_) == CodemodeDescribe.spell_reply(q) : String}
  LACdReply.cdy.answer(q)
