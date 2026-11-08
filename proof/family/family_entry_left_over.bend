# eukhe: the proof of LAW family_entry_left_over
#
# PROOF: the spelled request reads back with the rest untouched (fe.req_rt); the rest is not empty, so the entry answers the error form.

import Base
import ../../bend/family.bend as F
import ../../bend/ffi_family.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/family.bend as Family
import ./base/entry.bend as LE


def Family.family_entry_left_over(q, ch, t, fit):
  %Equal.sym(Wr.Dec<FF.Req>, FF.get_req(Family.fam_w_req(q, SCon{ch, t})), Wr.Got{q, SCon{ch, t}}, LE.fe.req_rt(q, SCon{ch, t}, fit)) : {FF.ffi.got(_) == Wr.err("family: malformed request") : String}
  {==}
