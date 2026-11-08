# eukhe: the proof of LAW stop_think_gives_up
#
# PROOF: the model's cap test is Nat's, so its rung test is the spec's rung_left; with none left the ladder quits.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../spec/harness/stop.bend as StSpec
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_think_gives_up(rc, shrink, lower, k, row, same, last, spent):
  +x = RnRecovery.Rk.longs(k, row)
  +m = RnRecovery.RCfg.long(rc)
  +r = {RnRecovery.Rec{k, row, same, last} : RnRecovery.Rec}
  %LA.stb.below(x, m) : {RnRecovery.rec.think(shrink, _, Bool.and(lower, Nat.is_eq(x, m)), x, same, last, r) == RnRecovery.Dec{RnRecovery.Quit{}, r} : RnRecovery.Dec}
  LA.stb.think_spent(shrink, Nat.is_lt(x, m), Bool.and(lower, Nat.is_eq(x, m)), x, same, last, r, spent)
