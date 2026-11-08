# eukhe: the proof of LAW stop_think_never_fails_early
#
# PROOF: the model's cap test is Nat's, so its rung test is the spec's rung_left; a rung that remains never quits.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../spec/harness/stop.bend as StSpec
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_think_never_fails_early(rc, shrink, lower, k, row, same, last, left):
  +x = RnRecovery.Rk.longs(k, row)
  +m = RnRecovery.RCfg.long(rc)
  +r = {RnRecovery.Rec{k, row, same, last} : RnRecovery.Rec}
  %LA.stb.below(x, m) : {Stop.quits(RnRecovery.Dec.act(RnRecovery.rec.think(shrink, _, Bool.and(lower, Nat.is_eq(x, m)), x, same, last, r))) == False{} : Bool}
  LA.stb.think_left(shrink, Nat.is_lt(x, m), Bool.and(lower, Nat.is_eq(x, m)), x, same, last, r, left)
