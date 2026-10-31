# eukhe: the proof of LAW arg_repair_entry_left_over
#
# PROOF: the spelled request reads back with the rest untouched
# (ae.req_rt); the rest is not empty, so the entry answers the error form.

import Base
import ../../bend/arg_repair.bend as Ar
import ../../bend/ffi_arg_repair.bend as FAr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/arg_repair.bend as ArgRepair
import ./base/entry.bend as AE

def ArgRepair.arg_repair_entry_left_over(q, c, t, fit):
  %Equal.sym(Wr.Dec<FAr.Req>, FAr.get_req(ArgRepair.ar_w_req(q, SCon{c, t})), Wr.Got{q, SCon{c, t}}, AE.ae.req_rt(q, SCon{c, t}, fit)) : {FAr.ffi.got(_) == Wr.err("arg_repair: malformed request") : String}
  {==}
