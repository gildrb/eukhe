# eukhe: the proof of LAW rec_leak_retries_with_a_note

import Base
import ../../bend/run.bend as Rn
import ../../laws/screen.bend as Screen

def leak_retries_with_a_note(+rc: Rn.RCfg, +h: Nat, kept: Bool, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, under: {Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)) == True{} : Bool}) -> {Rn.Rec.step(rc, Rn.Leak{False{}, h, kept}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Leaks{}, 1n+Rn.Rk.leaks(k, row), same, last}} : Rn.Dec}:
  %Equal.sym(Bool, Rn.below(Rn.Rk.leaks(k, row), Rn.RCfg.leak(rc)), True{}, under) : {Rn.rec.leak(_, Rn.Rk.leaks(k, row), same, last, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Leaks{}, 1n+Rn.Rk.leaks(k, row), same, last}} : Rn.Dec}
  {==}

def Screen.rec_leak_retries_with_a_note(rc, h, kept, k, row, same, last, under):
  leak_retries_with_a_note(rc, h, kept, k, row, same, last, under)
