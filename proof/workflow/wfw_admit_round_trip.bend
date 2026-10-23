# eukhe: the proof of LAW wfw_admit_round_trip

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def Workflow.wfw_admit_round_trip(a, rest, h):
  match a:
    case W.Ended{}:
      {==}
    case W.Reattach{}:
      {==}
    case W.Reuse{+i}:
      %LA.pww.nat(i, rest, h) : {FW.get_admit.reuse(_) == Wr.Got{W.Reuse{i}, rest} : Wr.Dec<W.Admit>}
      {==}
    case W.Spawn{}:
      {==}
    case W.Refused{}:
      {==}
