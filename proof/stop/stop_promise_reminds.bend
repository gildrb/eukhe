# eukhe: the proof of LAW stop_promise_reminds
#
# PROOF: the cap test is rewritten with its premise; the recovery computes.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../spec/harness/stop.bend as StSpec
import ../../laws/stop.bend as Stop

def Stop.stop_promise_reminds(rc, k, row, same, last, under):
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.promises(k, row), StSpec.promise_cap()), True{}, under) : {RnRecovery.rec.promise(_, RnRecovery.Rk.promises(k, row), same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Remind{}, RnRecovery.Rec{RnRecovery.Promises{}, 1n+RnRecovery.Rk.promises(k, row), same, last}} : RnRecovery.Dec}
  {==}
