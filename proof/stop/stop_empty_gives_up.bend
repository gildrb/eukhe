# eukhe: the proof of LAW stop_empty_gives_up
#
# PROOF: the cap test is rewritten with its premise; the recovery computes.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../spec/harness/stop.bend as StSpec
import ../../laws/stop.bend as Stop

def Stop.stop_empty_gives_up(rc, k, row, same, last, over):
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.empties(k, row), StSpec.empty_cap()), False{}, over) : {RnRecovery.Dec.act(RnRecovery.rec.empty(_, RnRecovery.Rk.empties(k, row), same, last, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}
  {==}
