# eukhe: the proof of LAW wfw_left_over

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def Workflow.wfw_left_over(r, c, rest, h):
  %LA.pww.req(r, SCon{c, rest}, h) : {FW.ffi.go(_) == Wr.err("workflow: input left over") : String}
  {==}
