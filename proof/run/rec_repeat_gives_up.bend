# eukhe: the proof of LAW rec_repeat_gives_up

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def repeat_gives_up(+rc: Rn.RCfg, +h: Nat, kept: Bool, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}, over: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == False{} : Bool}) -> {Rn.Dec.act(Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}:
  %Equal.sym(Bool, Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)), False{}, rep) : {Rn.Dec.act(Rn.rec.ran(_, Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}
  %Equal.sym(Bool, Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), False{}, over) : {Rn.Dec.act(Rn.rec.ran(False{}, _, kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last})) == Rn.Quit{} : Rn.Act}
  {==}

def Laws.rec_repeat_gives_up(rc, h, kept, k, row, same, last, rep, over):
  repeat_gives_up(rc, h, kept, k, row, same, last, rep, over)
