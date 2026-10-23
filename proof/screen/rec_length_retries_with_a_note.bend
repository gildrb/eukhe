# eukhe: the proof of LAW rec_length_retries_with_a_note

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/screen.bend as Screen

# The one-step laws
# -----------------

def length_retries_with_a_note(+rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, under: {RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)) == True{} : Bool}) -> {RnRecovery.Rec.step(rc, RnRecovery.Long{}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+RnRecovery.Rk.longs(k, row), same, last}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), True{}, under) : {RnRecovery.rec.long(_, RnRecovery.Rk.longs(k, row), same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n+RnRecovery.Rk.longs(k, row), same, last}} : RnRecovery.Dec}
  {==}

# (H4.8) A stuck model gets a recovery, each with a cap

def Screen.rec_length_retries_with_a_note(rc, k, row, same, last, under):
  length_retries_with_a_note(rc, k, row, same, last, under)
