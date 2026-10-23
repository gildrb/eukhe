# eukhe: the proof of LAW wfw_answers_admit

import Base
import ../../bend/workflow.bend as W
import ../../bend/ffi_workflow.bend as FW
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.wfw_answers_admit(prior, k, rows, p, h):
  %LA.pww.req(FW.AdmitReq{prior, k, rows, p}, "", h) : {FW.ffi.go(_) == FW.put_decision(W.admit(prior, k, rows, p), "") : String}
  {==}
