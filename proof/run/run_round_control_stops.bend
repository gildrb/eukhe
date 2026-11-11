# eukhe: the proof of LAW run_round_control_stops
#
# PROOF: a control makes the round's end Stops, which answers the run (by computation).

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/model.bend as Run
import ./base.bend as LA

def Run.run_round_control_stops(l, count, reset):
  {==}
