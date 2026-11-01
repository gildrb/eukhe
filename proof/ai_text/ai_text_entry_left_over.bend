# eukhe: the proof of LAW ai_text_entry_left_over

import Base
import ../../bend/ffi_ai_text.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/ai_text.bend as AiText
import ./base/entry.bend as LE

def AiText.ai_text_entry_left_over(q, rest, h, more):
  %Equal.sym(Wr.Dec<FT.Req>, FT.get_req(AiText.sp_w_req(q, rest)), Wr.Got{q, rest}, LE.aite.req_rt(q, rest, h)) : {FT.ffi.got(_) == Wr.err("ai_text: malformed request") : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FT.ffi.done(q, _) == Wr.err("ai_text: malformed request") : String}
  {==}
