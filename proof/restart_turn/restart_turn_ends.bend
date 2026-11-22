# eukhe: the proof of LAW restart_turn_ends
#
# PROOF: spent picks the code's end.

import Base
import ../../bend/restart_turn.bend as Rt
import ../../laws/restart_turn.bend as RestartTurn

def RestartTurn.restart_turn_ends(made, spent):
  %spent : {Rt.next(Rt.Reopened{made}) == Rt.reopened(_, made) : Rt.Next}
  {==}
