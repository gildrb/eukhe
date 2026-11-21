# eukhe: the proof of LAW stop_repeat_progress_restarts
#
# PROOF: the calls are fresh (the premise), so they run, and results that changed start a row of 1 (ran.same).

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

# fresh calls whose results changed run and start a row of 1
def str.ran_fresh(fresh: Bool, under: Bool, +m: Nat, +h: Nat, +n: Nat, +same: Nat, +last: Nat, r: RnRecovery.Rec, e: {fresh == True{} : Bool}) -> {RnRecovery.rec.ran(fresh, under, False{}, m, h, n, same, last, r) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n, h}} : RnRecovery.Dec}:
  match fresh:
    case True{}:
      {==}
    case False{}:
      LR.str.absurd({RnRecovery.rec.ran(False{}, under, False{}, m, h, n, same, last, r) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n, h}} : RnRecovery.Dec}, e)

def StopRecover.stop_repeat_progress_restarts(rc, h, k, row, same, last, fresh):
  match rc:
    case RnRecovery.RCfg{l, le, re, rp}:
      str.ran_fresh(RnRecovery.below(RnRecovery.again(same, last, h), rp), RnRecovery.below(RnRecovery.Rk.loops(k, row), re), RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last}, fresh)
