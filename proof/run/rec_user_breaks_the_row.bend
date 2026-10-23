# eukhe: the proof of LAW rec_user_breaks_the_row

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def user_breaks_the_row(+rc: Rn.RCfg, +k: Rn.Rk, +row: Nat, same: Nat, +last: Nat) -> {Rn.Dec.r(Rn.Rec.step(rc, Rn.Said{}, Rn.Rec{k, row, same, last})) == Rn.Rec{k, row, 0n, last} : Rn.Rec}:
  {==}

def Laws.rec_user_breaks_the_row(rc, k, row, same, last):
  user_breaks_the_row(rc, k, row, same, last)
