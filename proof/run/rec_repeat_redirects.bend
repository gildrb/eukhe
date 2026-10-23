# eukhe: the proof of LAW rec_repeat_redirects

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

def repeat_redirects(+rc: RnRecovery.RCfg, +h: Nat, kept: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)) == False{} : Bool}, under: {RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)) == True{} : Bool}) -> {RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+RnRecovery.Rk.loops(k, row), same, last}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), False{}, rep) : {RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+RnRecovery.Rk.loops(k, row), same, last}} : RnRecovery.Dec}
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), True{}, under) : {RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+RnRecovery.Rk.loops(k, row), same, last}} : RnRecovery.Dec}
  {==}

def Run.rec_repeat_redirects(rc, h, kept, k, row, same, last, rep, under):
  repeat_redirects(rc, h, kept, k, row, same, last, rep, under)
