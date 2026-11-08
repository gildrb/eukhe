# eukhe: the proof of LAW stop_lower_spends_a_note
#
# PROOF: the lower rung is the noted error; its step computes.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/stop.bend as Stop

def Stop.stop_lower_spends_a_note(cfg, pass, r, c, a, m, p):
  {==}
