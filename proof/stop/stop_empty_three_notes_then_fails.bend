# eukhe: the proof of LAW stop_empty_three_notes_then_fails
#
# PROOF: every note that is no empty note counts no empty note: the first empty reply gets note 1; the rows 1 to 3 compute.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_empty_three_notes_then_fails(rc, k, row, other):
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      LR.str.absurd_t({[RnDecision.decide.recover(rc, RnDecision.Emptied{}, RnRecovery.Empties{}, row), RnDecision.decide.recover(rc, RnDecision.Emptied{}, RnRecovery.Empties{}, 1n), RnDecision.decide.recover(rc, RnDecision.Emptied{}, RnRecovery.Empties{}, 2n), RnDecision.decide.recover(rc, RnDecision.Emptied{}, RnRecovery.Empties{}, 3n)] == [RnDecision.Redoes{1n}, RnDecision.Redoes{2n}, RnDecision.Redoes{3n}, RnDecision.Quits{}] : List<&2, RnDecision.Help>}, other)
