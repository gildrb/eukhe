# eukhe: the proof of LAW rec_repeat_redirects_then_fails
#
# PROOF: rounds in a row of repeat or more are no fresh calls (LRR.rr.rep_off); then as for a length stop (LRR.rr.rep_first, LRR.rr.rep_go, LRR.rr.rep_past), with the redirect cap.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/recover.bend as RunRecover
import ./base/recover.bend as LRR

def RunRecover.rec_repeat_redirects_then_fails(rc, before, k, row, x, rep, other):
  match rc:
    case RnRecovery.RCfg{+long, +le, +re, +rp}:
      (LRR.rr.rep_part(k, row, before, long, le, re, rp, rep, other), LRR.rr.rep_past(re, x, before, long, le, rp, rep))
