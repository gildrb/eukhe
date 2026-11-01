# eukhe: the proof of LAW stop_shrink_compacts_once
#
# PROOF: the compaction rung is the overflow with a cut; its step computes.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/stop.bend as Stop

def Stop.stop_shrink_compacts_once(cfg, pass, r, c, a, n, p):
  {==}
