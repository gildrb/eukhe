# eukhe: the proof of LAW rec_length_retries_with_a_note

import Base
import ../../bend/run.bend as Rn
import ../../laws/screen.bend as Screen

# The one-step laws
# -----------------

def length_retries_with_a_note(+rc: Rn.RCfg, +k: Rn.Rk, +row: Nat, +same: Nat, +last: Nat, under: {Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)) == True{} : Bool}) -> {Rn.Rec.step(rc, Rn.Long{}, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Longs{}, 1n+Rn.Rk.longs(k, row), same, last}} : Rn.Dec}:
  %Equal.sym(Bool, Rn.below(Rn.Rk.longs(k, row), Rn.RCfg.long(rc)), True{}, under) : {Rn.rec.long(_, Rn.Rk.longs(k, row), same, last, Rn.Rec{k, row, same, last}) == Rn.Dec{Rn.Redo{}, Rn.Rec{Rn.Longs{}, 1n+Rn.Rk.longs(k, row), same, last}} : Rn.Dec}
  {==}

# (H4.8) A stuck model gets a recovery, each with a cap

def Screen.rec_length_retries_with_a_note(rc, k, row, same, last, under):
  length_retries_with_a_note(rc, k, row, same, last, under)
