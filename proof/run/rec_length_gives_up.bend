# eukhe: the proof of LAW rec_length_gives_up

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def length_gives_up(+rc: Rn.RCfg, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, over: {Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)) == False{} : Bool}) -> {Rn.Dec.act(Rn.Rec.step(rc, Rn.Long{}, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}:
  %Equal.sym(Bool, Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)), False{}, over) : {Rn.Dec.act(Rn.rec.long(_, Rn.Rk.longs(k, row), same, last, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}
  {==}

def Run.rec_length_gives_up(rc, k, row, same, last, over):
  length_gives_up(rc, k, row, same, last, over)
