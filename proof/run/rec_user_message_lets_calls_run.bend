# eukhe: the proof of LAW rec_user_message_lets_calls_run
#
# PROOF: a user message clears the rounds in a row, so the next calls make a row of 1, below a cap past 1, and run (LR.str.ran_one).

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR

# the first of two facts
def uml.fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def RunRecover.rec_user_message_lets_calls_run(rc, h, kept, r, two):
  match rc:
    case RnRecovery.RCfg{+l0, +le, +re, +rp}:
      match r:
        case RnRecovery.Rec{+k, +row, same, +last}:
          uml.fst({RnRecovery.Dec.act(RnRecovery.rec.ran(RnRecovery.below(1n, rp), RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, 1n, h, RnRecovery.Rk.loops(k, row), 0n, last, RnRecovery.Rec{k, row, 0n, last})) == RnRecovery.Exec{} : RnRecovery.Act}, {RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.ran(RnRecovery.below(1n, rp), RnRecovery.below(RnRecovery.Rk.loops(k, row), re), kept, 1n, h, RnRecovery.Rk.loops(k, row), 0n, last, RnRecovery.Rec{k, row, 0n, last}))) == 1n : Nat}, LR.str.ran_one(kept, h, RnRecovery.Rk.loops(k, row), 0n, last, rp, RnRecovery.below(RnRecovery.Rk.loops(k, row), re), RnRecovery.Rec{k, row, 0n, last}, LR.str.lt_below(1n, rp, two)))
