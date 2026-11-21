# eukhe: the proof of LAW stop_think_row_starts_at_one
#
# PROOF: by cases on the note: after any note but a length note the length notes in a row are 0, below a cap of 1 + lg, so the length stop gets note 1 at its level; a length note contradicts the premise.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_think_row_starts_at_one(lg, lk, rd, rp, lower, k, row, same, last, other):
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      LR.str.absurd_t({RnRecovery.Rec.step(RnRecovery.RCfg{1n+lg, lk, rd, rp}, RnRecovery.Think{False{}, lower}, RnRecovery.Rec{RnRecovery.Longs{}, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Longs{}, 1n, same, last}} : RnRecovery.Dec}, other)
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      {==}
