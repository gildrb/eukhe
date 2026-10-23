# eukhe: the proof of LAW rec_user_breaks_the_row

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

def user_breaks_the_row(+rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, same: Nat, +last: Nat) -> {RnRecovery.Dec.r(RnRecovery.Rec.step(rc, RnRecovery.Said{}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Rec{k, row, 0n, last} : RnRecovery.Rec}:
  {==}

def Run.rec_user_breaks_the_row(rc, k, row, same, last):
  user_breaks_the_row(rc, k, row, same, last)
