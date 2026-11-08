# eukhe: the proof of LAW kin_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (ke.req_rt), so the entry answers the core's decision or landing, spelled as the laws spell it (ke.answer).

import Base
import ../../bend/kin.bend as K
import ../../bend/ffi_kin.bend as FK
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/kin.bend as Kin
import ./base/entry.bend as LE


def Kin.kin_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FK.Req>, FK.get_req(Kin.kin_w_req(q, "")), Wr.Got{q, ""}, LE.ke.req_rt(q, "", fit)) : {FK.ffi.got(_) == Kin.kin_w_reply(q) : String}
  LE.ke.answer(q)
