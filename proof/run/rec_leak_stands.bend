# eukhe: the proof of LAW rec_leak_stands

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def leak_stands(+rc: Rn.RCfg, +h: Nat, kept: Bool, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, over: {Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)) == False{} : Bool}) -> {Rn.Dec.act(Rn.Rec.step(rc, Rn.Leak{False{}, h, kept}, Rn.Rec{k, row, same, last})) == Rn.Stand{} : Rn.Act}:
  %Equal.sym(Bool, Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)), False{}, over) : {Rn.Dec.act(Rn.rec.leak(_, Rn.Rk.leaks(k, row), same, last, Rn.Rec{k, row, same, last})) == Rn.Stand{} : Rn.Act}
  {==}

def Run.rec_leak_stands(rc, h, kept, k, row, same, last, over):
  leak_stands(rc, h, kept, k, row, same, last, over)
