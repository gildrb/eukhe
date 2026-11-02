# eukhe: the proof of LAW model_name_entry_decides
#
# PROOF: the spelled request reads back whole (mne.req_rt), nothing is
# left, and the answer is the spelled spec answer (mne.answer).

import Base
import ../../bend/ffi_model_name.bend as FM
import ../../bend/wire.bend as Wr
import ../../laws/model_name.bend as ModelName
import ./base/entry.bend as LE

def ModelName.model_name_entry_decides(q, h):
  %Equal.sym(Wr.Dec<FM.Req>, FM.get_req(ModelName.sp_w_req(q, "")), Wr.Got{q, ""}, LE.mne.req_rt(q, "", h)) : {FM.ffi.got(_) == ModelName.sp_w_reply(q) : String}
  LE.mne.answer(q)
