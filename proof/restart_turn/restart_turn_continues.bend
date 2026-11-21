# eukhe: the proof of LAW restart_turn_continues
#
# PROOF: below picks the code's continue.

import Base
import ../../bend/restart_turn.bend as Rt
import ../../laws/restart_turn.bend as RestartTurn

def RestartTurn.restart_turn_continues(made, below):
  %below : {Rt.next(Rt.Reopened{made}) == Rt.reopened(_, made) : Rt.Next}
  {==}
