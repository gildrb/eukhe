# eukhe: the proof of LAW wfw_malformed

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../laws/workflow.bend as Workflow

def Workflow.wfw_malformed(s, h):
  %Equal.sym(Wr.Dec<FW.Req>, FW.get_req(s), Wr.Bad{}, h) : {FW.ffi.go(_) == Wr.err("workflow: malformed request") : String}
  {==}
