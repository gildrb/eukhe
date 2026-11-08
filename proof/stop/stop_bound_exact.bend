# eukhe: the proof of LAW stop_bound_exact
#
# PROOF: by cases on the window: unknown (0) or known; both sides compute.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../spec/harness/stop.bend as StSpec
import ../../laws/stop.bend as Stop

def Stop.stop_bound_exact(window, catalog, prompt, out):
  match window:
    case 0n:
      {==}
    case 1n+w:
      {==}
