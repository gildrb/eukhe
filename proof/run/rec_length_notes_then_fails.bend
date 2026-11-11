# eukhe: the proof of LAW rec_length_notes_then_fails
#
# PROOF: a note that is no length note starts the row as no note does (LRR.rr.long_first); from j notes with m under the cap, m notes then the run fails (LRR.rr.long_go, by induction on m); a row of the cap or past it fails the run (LRR.rr.long_past).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/recover.bend as RunRecover
import ./base/recover.bend as LRR

def RunRecover.rec_length_notes_then_fails(rc, k, row, x, other):
  match rc:
    case RnRecovery.RCfg{+long, +le, +re, +rp}:
      (LRR.rr.long_part(k, row, long, le, re, rp, other), LRR.rr.long_past(long, x, le, re, rp))
