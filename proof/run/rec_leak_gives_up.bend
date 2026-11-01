# eukhe: the proof of LAW rec_leak_gives_up

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

def leak_gives_up(+rc: RnRecovery.RCfg, +h: Nat, kept: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, over: {RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)) == False{} : Bool}) -> {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)), False{}, over) : {RnRecovery.Dec.act(RnRecovery.rec.leak(_, RnRecovery.Rk.leaks(k, row), same, last, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}
  {==}

def Run.rec_leak_gives_up(rc, h, kept, k, row, same, last, over):
  leak_gives_up(rc, h, kept, k, row, same, last, over)
