# eukhe: the proof of LAW wfw_answers_admit

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def Workflow.wfw_answers_admit(prior, k, rows, p, h):
  %LA.pww.req(FW.AdmitReq{prior, k, rows, p}, "", h) : {FW.ffi.go(_) == FW.put_decision(W.admit(prior, k, rows, p), "") : String}
  {==}
