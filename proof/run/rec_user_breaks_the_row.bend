# eukhe: the proof of LAW rec_user_breaks_the_row

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def user_breaks_the_row(+rc: Rn.RCfg, +k: Rn.Rk, +row: Nat, same: Nat, +last: Nat) -> {Rn.Dec.r(Rn.Rec.step(rc, Rn.Said{}, Rn.Rec{k, row, same, last})) == Rn.Rec{k, row, 0n, last} : Rn.Rec}:
  {==}

def Run.rec_user_breaks_the_row(rc, k, row, same, last):
  user_breaks_the_row(rc, k, row, same, last)
