# eukhe: the proof of LAW rec_leak_row_starts_at_one
#
# PROOF: by cases on the note: after any note but a leak note the leaks in a row are 0, below a cap of 1 + lk, so the leak gets note 1; a leak note contradicts the premise.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR

def RunRecover.rec_leak_row_starts_at_one(lg, lk, rd, rp, h, kept, k, row, same, last, other):
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      LR.str.absurd_t({RnRecovery.Rec.step(RnRecovery.RCfg{lg, 1n+lk, rd, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n, same, last}} : RnRecovery.Dec}, other)
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      {==}
