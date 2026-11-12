# eukhe: the proof of LAW stop_think_compacts_when_window_ran_out
#
# PROOF: the premises make the window test true (LR.str.bound_true); a cuttable stop whose window ran out compacts.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_think_compacts_when_window_ran_out(rc, w, c, p, o, lower, k, row, below, reach):
  %Equal.sym(Bool, RnRecovery.bound(1n+w, c, p, o), True{}, LR.str.bound_true(w, c, p, o, below, reach)) : {RnDecision.Help.of(RnRecovery.rec.go(rc, RnRecovery.Think{Bool.and(True{}, _), lower}, k, row, 0n, 0n)) == RnDecision.Compacts{} : RnDecision.Help}
  {==}
