# eukhe: the proof of LAW stop_promise_stands
#
# PROOF: the cap test is rewritten with its premise; the recovery computes.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../spec/harness/stop.bend as StSpec
import ../../laws/stop.bend as Stop

def Stop.stop_promise_stands(rc, k, row, same, last, over):
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.promises(k, row), StSpec.promise_cap()), False{}, over) : {RnRecovery.Dec.act(RnRecovery.rec.promise(_, RnRecovery.Rk.promises(k, row), same, last, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Stand{} : RnRecovery.Act}
  {==}
