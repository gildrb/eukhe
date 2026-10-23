# eukhe: the proof of LAW rec_repeat_never_runs

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run.bend as Run

# a repeat never runs, under the redirect cap or at it
def repeat_runs_not(u: Bool, -kept: Bool, -m: Nat, -h: Nat, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec) -> {RnRecovery.Act.runs(RnRecovery.Dec.act(RnRecovery.rec.ran(False{}, u, kept, m, h, n, same, last, r))) == False{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def repeat_never_runs(+rc: RnRecovery.RCfg, +h: Nat, kept: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)) == False{} : Bool}) -> {RnRecovery.Act.runs(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(same, last, h), RnRecovery.RCfg.repeat(rc)), False{}, rep) : {RnRecovery.Act.runs(RnRecovery.Dec.act(RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool}
  repeat_runs_not(RnRecovery.below(RnRecovery.Rk.loops(k, row), RnRecovery.RCfg.redirect(rc)), kept, RnRecovery.again(same, last, h), h, RnRecovery.Rk.loops(k, row), same, last, RnRecovery.Rec{k, row, same, last})

def Run.rec_repeat_never_runs(rc, h, kept, k, row, same, last, rep):
  repeat_never_runs(rc, h, kept, k, row, same, last, rep)
