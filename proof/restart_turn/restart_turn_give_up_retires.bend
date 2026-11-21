# eukhe: the proof of LAW restart_turn_give_up_retires
#
# PROOF: by the last relaunch: Clear contradicts h; the others compute.

import Base
import ../../bend/restart_turn.bend as Rt
import ../../laws/restart_turn.bend as RestartTurn
import ../base/staging.bend as LStg

def RestartTurn.restart_turn_give_up_retires(p, h):
  match p:
    case Rt.Clear{}:
      LStg.stg.absurd({Rt.next(Rt.GaveUp{Rt.Clear{}}) == Rt.Retire{} : Rt.Next}, h)
    case Rt.Unsettled{}:
      {==}
    case Rt.Ended{}:
      {==}
