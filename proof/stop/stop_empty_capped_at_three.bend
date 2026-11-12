# eukhe: the proof of LAW stop_empty_capped_at_three
#
# PROOF: a row of 3 + x is not below 3 (x is 0 or more); the recovery computes.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_empty_capped_at_three(rc, x):
  match x:
    case 0n:
      {==}
    case 1n++y:
      {==}
