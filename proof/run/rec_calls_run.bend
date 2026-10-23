# eukhe: the proof of LAW rec_calls_run

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

def calls_run(+rc: RnRecovery.RCfg, +h: Nat, +kept: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, fresh: {RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)) == True{} : Bool}) -> {RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, RnRecovery.ran.same(kept, RnRecovery.again(same, last, h)), h}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), True{}, fresh) : {RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, RnRecovery.ran.same(kept, RnRecovery.again(same, last, h)), h}} : RnRecovery.Dec}
  {==}

def Run.rec_calls_run(rc, h, kept, k, row, same, last, fresh):
  calls_run(rc, h, kept, k, row, same, last, fresh)
