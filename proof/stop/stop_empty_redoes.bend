# eukhe: the proof of LAW stop_empty_redoes
#
# PROOF: the cap test is rewritten with its premise; the recovery computes.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../spec/harness/stop.bend as StSpec
import ../../laws/stop.bend as Stop

def Stop.stop_empty_redoes(rc, k, row, same, last, under):
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.empties(k, row), StSpec.empty_cap()), True{}, under) : {RnRecovery.rec.empty(_, RnRecovery.Rk.empties(k, row), same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Empties{}, 1n+RnRecovery.Rk.empties(k, row), same, last}} : RnRecovery.Dec}
  {==}
