# eukhe: the proof of LAW rec_calls_run

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def calls_run(+rc: Rn.RCfg, +h: Nat, +kept: Bool, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, fresh: {Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)) == True{} : Bool}) -> {Rn.Rec.step(rc, Rn.Ran{h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Exec{}, Rn.Rec{Rn.Free{}, 0n, Rn.ran.same(kept, Rn.again(same, last, h)), h}} : Rn.Dec}:
  %Equal.sym(Bool, Rn.below(Rn.again(same, last, h), Rn.RCfg.repeat(rc)), True{}, fresh) : {Rn.rec.ran(_, Rn.below(Rn.Rk.loops(k, row), Rn.RCfg.redirect(rc)), kept, Rn.again(same, last, h), h, Rn.Rk.loops(k, row), same, last, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Exec{}, Rn.Rec{Rn.Free{}, 0n, Rn.ran.same(kept, Rn.again(same, last, h)), h}} : Rn.Dec}
  {==}

def Laws.rec_calls_run(rc, h, kept, k, row, same, last, fresh):
  calls_run(rc, h, kept, k, row, same, last, fresh)
