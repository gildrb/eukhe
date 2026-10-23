# eukhe: the proof of LAW rec_length_gives_up

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

def length_gives_up(+rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, over: {RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == False{} : Bool}) -> {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Long{}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), False{}, over) : {RnRecovery.Dec.act(RnRecovery.rec.long(_, RnRecovery.Rk.longs(k, row), same, last, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}
  {==}

def Run.rec_length_gives_up(rc, k, row, same, last, over):
  length_gives_up(rc, k, row, same, last, over)
