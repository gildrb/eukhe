# eukhe: the proof of LAW rec_leak_notes_then_fails
#
# PROOF: as for a length stop (LRR.rr.leak_first, LRR.rr.leak_go, LRR.rr.leak_past), with the leak cap.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/recover.bend as RunRecover
import ./base/recover.bend as LRR

def RunRecover.rec_leak_notes_then_fails(rc, k, row, x, other):
  match rc:
    case RnRecovery.RCfg{+long, +le, +re, +rp}:
      (LRR.rr.leak_part(k, row, long, le, re, rp, other), LRR.rr.leak_past(le, x, long, re, rp))
