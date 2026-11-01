# eukhe: the proof of LAW model_name_entry_left_over
#
# PROOF: the spelled request reads back (mne.req_rt) with the rest left
# over; a rest that is not empty is not the end, so the answer is the error.

import Base
import ../../bend/ffi_model_name.bend as FM
import ../../bend/wire.bend as Wr
import ../../laws/model_name.bend as ModelName
import ./base/entry.bend as LE

def ModelName.model_name_entry_left_over(q, rest, h, more):
  %Equal.sym(Wr.Dec<FM.Req>, FM.get_req(ModelName.sp_w_req(q, rest)), Wr.Got{q, rest}, LE.mne.req_rt(q, rest, h)) : {FM.ffi.got(_) == Wr.err("model_name: malformed request") : String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FM.ffi.done(q, _) == Wr.err("model_name: malformed request") : String}
  {==}
