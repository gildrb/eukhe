# eukhe: the proof of LAW stop_repeat_row_restarts
#
# PROOF: another hash makes a row of 1 whatever row came before; a row of 1 under a cap past 1 runs and keeps the row at 1 (LR.str.ran_one).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_repeat_row_restarts(rc, h, h2, kept, k, row, same, two, other):
  match rc:
    case RnRecovery.RCfg{l, le, re, rp}:
      match same:
        case 0n:
          LR.str.ran_one(kept, h2, RnRecovery.Rk.loops(k, row), 0n, h, rp, RnRecovery.below(RnRecovery.Rk.loops(k, row), re), RnRecovery.Rec{k, row, 0n, h}, LR.str.lt_below(1n, rp, two))
        case 1n++s:
          %Equal.sym(Bool, Nat.is_eq(h, h2), False{}, other) : {RnRecovery.Dec.act(RnRecovery.rec.ran(RnRecovery.below(RnRecovery.again.eq(_, s), rp), RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, RnRecovery.again.eq(_, s), h2, RnRecovery.Rk.loops(k, row), 1n+s, h, RnRecovery.Rec{k, row, 1n+s, h})) == RnRecovery.Exec{} : RnRecovery.Act} & {RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.ran(RnRecovery.below(RnRecovery.again.eq(_, s), rp), RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, RnRecovery.again.eq(_, s), h2, RnRecovery.Rk.loops(k, row), 1n+s, h, RnRecovery.Rec{k, row, 1n+s, h}))) == 1n : Nat}
          LR.str.ran_one(kept, h2, RnRecovery.Rk.loops(k, row), 1n+s, h, rp, RnRecovery.below(RnRecovery.Rk.loops(k, row), re), RnRecovery.Rec{k, row, 1n+s, h}, LR.str.lt_below(1n, rp, two))
