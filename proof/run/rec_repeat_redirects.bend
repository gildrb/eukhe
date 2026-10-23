# eukhe: the proof of LAW rec_repeat_redirects

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run

def repeat_redirects(+rc: Rn.RCfg, +h: Nat, kept: Bool, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}, under: {Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)) == True{} : Bool}) -> {Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Loops{}, 1n+Rn.Rk.loops(k, row), same, last}} : Rn.Dec}:
  %Equal.sym(Bool, Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)), False{}, rep) : {Rn.rec.ran(_, Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Loops{}, 1n+Rn.Rk.loops(k, row), same, last}} : Rn.Dec}
  %Equal.sym(Bool, Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), True{}, under) : {Rn.rec.ran(False{}, _, kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Loops{}, 1n+Rn.Rk.loops(k, row), same, last}} : Rn.Dec}
  {==}

def Run.rec_repeat_redirects(rc, h, kept, k, row, same, last, rep, under):
  repeat_redirects(rc, h, kept, k, row, same, last, rep, under)
