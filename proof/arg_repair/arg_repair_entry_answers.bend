# eukhe: the proof of LAW arg_repair_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (ae.req_rt), so the entry answers the model's verdict, which is the
# spec's (arg_repair_spec), encoded by encoders that are the spec spellers
# (ae.verdict).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../bend/ffi_arg_repair.bend as FAr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/arg_repair.bend as ArgRepair
import ./base/entry.bend as AE

def ArgRepair.arg_repair_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FAr.Req>, FAr.get_req(ArgRepair.ar_w_req(q, "")), Wr.Got{q, ""}, AE.ae.req_rt(q, "", fit)) : {FAr.ffi.got(_) == ArgRepair.ar_w_reply(q) : String}
  AE.ae.reply(q)
