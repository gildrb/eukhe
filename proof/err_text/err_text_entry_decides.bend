# eukhe: the proof of LAW err_text_entry_decides
#
# PROOF: the spelled request reads back whole, nothing left
# (LA.etb.req); the answer is the spelled spec answer (LA.etb.reply).

import Base
import ../../bend/ffi_err_text.bend as FE
import ../../bend/wire.bend as Wr
import ../../laws/err_text.bend as ErrText
import ./base.bend as LA

def ErrText.err_text_entry_decides(q, h):
  %Equal.sym(Wr.Dec<FE.Req>, FE.get_req(ErrText.sp_w_req(q, "")), Wr.Got{q, ""}, LA.etb.req(q, "", h)) : {FE.ffi.got(_) == ErrText.sp_w_reply(q) : String}
  LA.etb.reply(q)
