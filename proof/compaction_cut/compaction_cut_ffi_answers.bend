# eukhe: the proof of LAW compaction_cut_ffi_answers

import Base
import ../../bend/context_order.bend as Co
import ../../bend/compaction_cut.bend as Cc
import ../../bend/ffi_compaction_cut.bend as FCc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/context_order.bend as ContextOrder
import ../../laws/compaction_cut.bend as CompactionCut
import ../context_order/base.bend as LACo
import ./base/read.bend as LACcRead
import ./base/reply.bend as LACcReply

# PROOF of LAW compaction_cut_ffi_answers: the entry reads the request back whole with nothing left (cct.req) and answers the model's answer with encoders equal to the spec's spellers (ccr.answer).

def CompactionCut.compaction_cut_ffi_answers(q, h):
  %Equal.sym(Wr.Dec<FCc.Req>, FCc.get_req(CompactionCut.spell_req(q, "")), Wr.Got{q, ""}, LACcRead.cct.req(q, "", h)) : {FCc.ffi.got(_) == CompactionCut.spell_reply(q) : String}
  LACcReply.ccr.answer(q)
