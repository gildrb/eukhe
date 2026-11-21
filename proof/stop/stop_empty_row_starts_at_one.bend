# eukhe: the proof of LAW stop_empty_row_starts_at_one
#
# PROOF: by cases on the note: after any note but an empty note the empties in a row are 0, below the cap of 3, so the empty reply gets note 1; an empty note contradicts the premise.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_empty_row_starts_at_one(rc, k, row, same, last, other):
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      LR.str.absurd_t({RnRecovery.Rec.step(rc, RnRecovery.Empty{}, RnRecovery.Rec{RnRecovery.Empties{}, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Empties{}, 1n, same, last}} : RnRecovery.Dec}, other)
