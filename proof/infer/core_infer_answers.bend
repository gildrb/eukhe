# eukhe: the proof of LAW core_infer_answers

import Base
import ../../bend/infer.bend as If
import ../../bend/ffi_infer.bend as FIn
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.core_infer_answers(cap, ts, need, h):
  %LA.pc.i_req(FIn.Req{cap, ts, need}, "", h) : {FIn.ffi.go(_) == FIn.put_plan(If.plan(cap, ts, need), "") : String}
  {==}
