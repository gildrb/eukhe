# eukhe: the proof of LAW stop_capped_past_the_cap
#
# PROOF: each bound plus x is not below the bound (LR.str.past).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_capped_past_the_cap(rc, x):
  match rc:
    case RnRecovery.RCfg{l, le, re, rp}:
      (LR.str.past(2n+l, x), LR.str.past(1n+le, x), LR.str.past(1n+re, x), LR.str.past(4n, x))
