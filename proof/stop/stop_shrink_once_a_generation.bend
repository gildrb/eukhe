# eukhe: the proof of LAW stop_shrink_once_a_generation
#
# PROOF: the compaction rung's reply is a cut overflow; the generation has one compaction left until it compacted; both sides compute.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_shrink_once_a_generation(l, at, notes, waited, pass):
  ({==}, {==})
