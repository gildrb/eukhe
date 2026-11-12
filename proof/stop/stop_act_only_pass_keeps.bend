# eukhe: the proof of LAW stop_act_only_pass_keeps
#
# PROOF: act by act, both sides compute (LR.str.helps_plain); Pass returns the reply it was given.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_act_only_pass_keeps(a, q):
  (LR.str.helps_plain(a), {==})
