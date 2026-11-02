# eukhe: the proof of LAW stop_act_runs_exact
#
# PROOF: act by act, both sides compute.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/stop.bend as Stop

def stp.act_runs(a: RnRecovery.Act) -> {RnRecovery.Act.runs(a) == Stop.spec_runs(a) : Bool}:
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

def Stop.stop_act_runs_exact(a):
  stp.act_runs(a)
