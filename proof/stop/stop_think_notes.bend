# eukhe: the proof of LAW stop_think_notes
#
# PROOF: the cap test is rewritten with its premise; the ladder computes.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/stop.bend as Stop

def Stop.stop_think_notes(rc, lower, k, row, same, last, under):
  +x = RnRecovery.Rk.longs(k, row)
  +m = RnRecovery.RCfg.long(rc)
  %Equal.sym(Bool, RnRecovery.below(x, m), True{}, under) : {RnRecovery.rec.think(False{}, _, Bool.and(lower, Nat.is_eq(x, m)), x, same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+x, same, last}} : RnRecovery.Dec}
  {==}
