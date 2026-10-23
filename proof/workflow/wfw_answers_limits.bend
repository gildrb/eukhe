# eukhe: the proof of LAW wfw_answers_limits

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def Workflow.wfw_answers_limits(c, m, cap, h):
  %LA.pww.req(FW.LimitsReq{c, m, cap}, "", h) : {FW.ffi.go(_) == FW.put_limits(W.effective(W.Limits{c, m}, cap), "") : String}
  {==}
