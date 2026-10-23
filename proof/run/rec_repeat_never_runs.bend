# eukhe: the proof of LAW rec_repeat_never_runs

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

# a repeat never runs, under the redirect cap or at it
def repeat_runs_not(u: Bool, -kept: Bool, -m: Nat, -h: Nat, -n: Nat, -same: Nat, -last: Nat, -r: Rn.Rec) -> {Rn.Act.runs(Rn.Dec.act(Rn.rec.ran(False{}, u, kept, m, h, n, same, last, r))) == False{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def repeat_never_runs(+rc: Rn.RCfg, +h: Nat, kept: Bool, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, rep: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == False{} : Bool}) -> {Rn.Act.runs(Rn.Dec.act(Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}))) == False{} : Bool}:
  %Equal.sym(Bool, Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)), False{}, rep) : {Rn.Act.runs(Rn.Dec.act(Rn.rec.ran(_, Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last}))) == False{} : Bool}
  repeat_runs_not(Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last})

def Laws.rec_repeat_never_runs(rc, h, kept, k, row, same, last, rep):
  repeat_never_runs(rc, h, kept, k, row, same, last, rep)
