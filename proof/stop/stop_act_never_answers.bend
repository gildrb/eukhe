# eukhe: the proof of LAW stop_act_never_answers
#
# PROOF: act by act at any counts (LR.str.never_answers): Pass does not help; Exec's calls go to the tools; a noted retry, a failure and a compaction are no answer, whatever count is left.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_act_never_answers(a, q, l, t, helps):
  LR.str.never_answers(a, q, RnDecision.Lim.cfg(l), 0n, RnDecision.At.c(t), RnDecision.At.a(l, t), RnDecision.At.n(l, t), RnDecision.At.p(l, t), helps)
