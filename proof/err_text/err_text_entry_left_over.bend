# eukhe: the proof of LAW err_text_entry_left_over
#
# PROOF: the spelled request reads back with the rest after it
# (LA.etb.req); the rest is not empty, so the entry answers the error.

import Base
import ../../bend/ffi_err_text.bend as FE
import ../../bend/wire.bend as Wr
import ../../laws/err_text.bend as ErrText
import ./base.bend as LA

def ErrText.err_text_entry_left_over(q, rest, h, more):
  %Equal.sym(Wr.Dec<FE.Req>, FE.get_req(ErrText.sp_w_req(q, rest)), Wr.Got{q, rest}, LA.etb.req(q, rest, h)) : {FE.ffi.got(_) == Wr.err("err_text: malformed request") : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FE.ffi.done(q, _) == Wr.err("err_text: malformed request") : String}
  {==}
