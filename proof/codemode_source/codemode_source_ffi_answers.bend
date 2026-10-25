# eukhe: the proof of LAW codemode_source_ffi_answers

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/ffi_codemode_source.bend as FSrc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ../context_order/base.bend as LACo
import ./base/read.bend as LACsRead
import ./base/reply.bend as LACsReply

# PROOF of LAW codemode_source_ffi_answers: the entry reads the request back whole with nothing left (csq.req) and answers the model's answer with an encoder equal to the spec's speller (csy.answer).

def CodemodeSource.codemode_source_ffi_answers(f, h):
  %Equal.sym(Wr.Dec<Src.Facts>, FSrc.get_req(CodemodeSource.spell_req(f, "")), Wr.Got{f, ""}, LACsRead.csq.req(f, "", h)) : {FSrc.ffi.got(_) == CodemodeSource.spell_reply(f) : String}
  LACsReply.csy.answer(Src.parse(f))
