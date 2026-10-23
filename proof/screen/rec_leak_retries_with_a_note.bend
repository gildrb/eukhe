# eukhe: the proof of LAW rec_leak_retries_with_a_note

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/screen.bend as Screen

def leak_retries_with_a_note(+rc: RnRecovery.RCfg, +h: Nat, kept: Bool, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat, under: {RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)) == True{} : Bool}) -> {RnRecovery.Rec.step(rc, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+RnRecovery.Rk.leaks(k, row), same, last}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)), True{}, under) : {RnRecovery.rec.leak(_, RnRecovery.Rk.leaks(k, row), same, last, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n+RnRecovery.Rk.leaks(k, row), same, last}} : RnRecovery.Dec}
  {==}

def Screen.rec_leak_retries_with_a_note(rc, h, kept, k, row, same, last, under):
  leak_retries_with_a_note(rc, h, kept, k, row, same, last, under)
