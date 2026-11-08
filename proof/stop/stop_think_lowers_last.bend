# eukhe: the proof of LAW stop_think_lowers_last
#
# PROOF: a row at the cap is not under it; both tests are rewritten; the ladder computes.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_think_lowers_last(rc, k, row, same, last, at):
  +x = RnRecovery.Rk.longs(k, row)
  +m = RnRecovery.RCfg.long(rc)
  %Equal.sym(Bool, RnRecovery.below(x, m), False{}, LA.stb.eq_not_below(x, m, at)) : {RnRecovery.rec.think(False{}, _, Bool.and(True{}, Nat.is_eq(x, m)), x, same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Lower{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+x, same, last}} : RnRecovery.Dec}
  %Equal.sym(Bool, Nat.is_eq(x, m), True{}, at) : {RnRecovery.rec.think(False{}, False{}, Bool.and(True{}, _), x, same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Lower{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+x, same, last}} : RnRecovery.Dec}
  {==}
