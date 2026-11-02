# eukhe: the proof of LAW ai_text_entry_decides
#
# PROOF: the spelled request reads back whole (awe.req_rt), nothing is left,
# and the answer is the spelled model answer (awe.answer).

import Base
import ../../bend/ffi_ai_text.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/ai_text.bend as AiText
import ./base/entry.bend as LE

def AiText.ai_text_entry_decides(q, h):
  %Equal.sym(Wr.Dec<FT.Req>, FT.get_req(AiText.sp_w_req(q, "")), Wr.Got{q, ""}, LE.aite.req_rt(q, "", h)) : {FT.ffi.got(_) == AiText.sp_w_reply(q) : String}
  LE.aite.answer(q)
