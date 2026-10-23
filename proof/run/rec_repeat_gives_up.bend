# eukhe: the proof of LAW rec_repeat_gives_up

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

def repeat_gives_up(+rc: RnRecovery.RCfg, +h: Nat, kept: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)) == False{} : Bool}, over: {RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)) == False{} : Bool}) -> {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), False{}, rep) : {RnRecovery.Dec.act(RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), False{}, over) : {RnRecovery.Dec.act(RnRecovery.rec.ran(False{}, _, kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Quit{} : RnRecovery.Act}
  {==}

def Run.rec_repeat_gives_up(rc, h, kept, k, row, same, last, rep, over):
  repeat_gives_up(rc, h, kept, k, row, same, last, rep, over)
