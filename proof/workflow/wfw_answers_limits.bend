# eukhe: the proof of LAW wfw_answers_limits

import Base
import ../../bend/workflow.bend as W
import ../../bend/ffi_workflow.bend as FW
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.wfw_answers_limits(c, m, cap, h):
  %LA.pww.req(FW.LimitsReq{c, m, cap}, "", h) : {FW.ffi.go(_) == FW.put_limits(W.effective(W.Limits{c, m}, cap), "") : String}
  {==}
