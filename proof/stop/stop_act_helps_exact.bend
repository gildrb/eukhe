# eukhe: the proof of LAW stop_act_helps_exact
#
# PROOF: act by act, both sides compute.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/stop.bend as Stop

def stp.act_helps(a: RnRecovery.Act) -> {RnRecovery.Act.helps(a) == Stop.spec_helps(a) : Bool}:
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

def Stop.stop_act_helps_exact(a):
  stp.act_helps(a)
