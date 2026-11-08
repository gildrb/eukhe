# eukhe: the proof of LAW stop_think_lowers_once
#
# PROOF: a row one past the cap is neither under it nor at it; the ladder quits whatever the level.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def once(l: Bool, -x: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RnRecovery.Dec.act(RnRecovery.rec.think(False{}, False{}, Bool.and(l, False{}), x, same, last, r)) == RnRecovery.Quit{} : RnRecovery.Act}:
  match l:
    case True{}:
      {==}
    case False{}:
      {==}

def Stop.stop_think_lowers_once(rc, lower, same, last):
  +m = RnRecovery.RCfg.long(rc)
  +r = {RnRecovery.Rec{RnRecovery.Longs{}, 1n+m, same, last} : RnRecovery.Rec}
  %Equal.sym(Bool, RnRecovery.below(1n+m, m), False{}, LA.stb.succ_not_below(m)) : {RnRecovery.Dec.act(RnRecovery.rec.think(False{}, _, Bool.and(lower, Nat.is_eq(1n+m, m)), 1n+m, same, last, r)) == RnRecovery.Quit{} : RnRecovery.Act}
  %Equal.sym(Bool, Nat.is_eq(1n+m, m), False{}, LA.stb.succ_not_eq(m)) : {RnRecovery.Dec.act(RnRecovery.rec.think(False{}, False{}, Bool.and(lower, _), 1n+m, same, last, r)) == RnRecovery.Quit{} : RnRecovery.Act}
  once(lower, 1n+m, same, last, r)
