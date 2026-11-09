# eukhe: the proof of LAW stop_act_runs_only_calls
#
# PROOF: act by act, both sides compute.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_act_runs_only_calls(a):
  match a:
    case RnRecovery.Pass{}:
      {==}
    case RnRecovery.Exec{}:
      {==}
    case RnRecovery.Redo{}:
      {==}
    case RnRecovery.Quit{}:
      {==}
    case RnRecovery.Shrink{}:
      {==}
    case RnRecovery.Lower{}:
      {==}
