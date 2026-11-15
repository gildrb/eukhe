# eukhe: the proof of LAW limits_entry_left_over
#
# PROOF: the spelled request reads back with the rest untouched
# (limits_entry_answers' lpe.req); the rest is not empty, so the entry
# answers the error form.

import Base
import ../../bend/ffi_limits.bend as FL
import ../../bend/wire.bend as Wr
import ../../laws/limits.bend as Limits
import ./limits_entry_answers.bend as PEntryAnswers

def Limits.limits_entry_left_over(q, ch, t, fit):
  %Equal.sym(Wr.Dec<FL.Req>, FL.get_req(Limits.sp_w_req(q, SCon{ch, t})), Wr.Got{q, SCon{ch, t}}, PEntryAnswers.lpe.req(q, SCon{ch, t}, fit)) : {FL.ffi.got(_) == Wr.err("limits: malformed request") : String}
  {==}
