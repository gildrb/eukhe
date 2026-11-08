# eukhe: the proof of LAW kin_entry_left_over
#
# PROOF: the spelled request reads back with the rest untouched (ke.req_rt); the rest is not empty, so the entry answers the error form.

import Base
import ../../bend/kin.bend as K
import ../../bend/ffi_kin.bend as FK
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/kin.bend as Kin
import ./base/entry.bend as LE


def Kin.kin_entry_left_over(q, ch, t, fit):
  %Equal.sym(Wr.Dec<FK.Req>, FK.get_req(Kin.kin_w_req(q, SCon{ch, t})), Wr.Got{q, SCon{ch, t}}, LE.ke.req_rt(q, SCon{ch, t}, fit)) : {FK.ffi.got(_) == Wr.err("kin: malformed request") : String}
  {==}
