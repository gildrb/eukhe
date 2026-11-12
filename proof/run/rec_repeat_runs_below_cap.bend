# eukhe: the proof of LAW rec_repeat_runs_below_cap
#
# PROOF: calls that make before + 1 < repeat rounds in a row are fresh (LRR.rr.rep_on), and fresh calls run whatever the note.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ../../laws/run/recover.bend as RunRecover
import ./base/recover.bend as LRR

def RunRecover.rec_repeat_runs_below_cap(rc, before, k, row, fresh):
  match rc:
    case RnRecovery.RCfg{+long, +le, +re, +rp}:
      %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(before, 0n, 0n), rp), True{}, LRR.rr.rep_on(before, rp, fresh)) : {RnDecision.Help.of(RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), re), True{}, RnRecovery.again(before, 0n, 0n), 0n, RnRecovery.Rk.loops(k, row), before, 0n, RnRecovery.Rec{k, row, before, 0n})) == RnDecision.Runs{} : RnDecision.Help}
      {==}
