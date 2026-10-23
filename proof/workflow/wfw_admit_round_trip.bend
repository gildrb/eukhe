# eukhe: the proof of LAW wfw_admit_round_trip

import Base
import ../../bend/workflow.bend as W
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.wfw_admit_round_trip(a, rest, h):
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
