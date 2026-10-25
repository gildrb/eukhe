# eukhe: the proof of LAW context_order_ffi_answers

import Base
import ../../bend/context_order.bend as Co
import ../../bend/ffi_context_order.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo
import ./base/read.bend as LACoRead
import ./base/reply.bend as LACoReply

# PROOF of LAW context_order_ffi_answers: the entry reads the request back whole with nothing left (cot.req) and answers the model's answer with encoders equal to the spec's spellers (cor.answer).

def ContextOrder.context_order_ffi_answers(q, h):
  %Equal.sym(Wr.Dec<FCo.Req>, FCo.get_req(ContextOrder.spell_req(q, "")), Wr.Got{q, ""}, LACoRead.cot.req(q, "", h)) : {FCo.ffi.got(_) == ContextOrder.spell_reply(q) : String}
  LACoReply.cor.answer(q)
