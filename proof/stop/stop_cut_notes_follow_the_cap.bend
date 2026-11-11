# eukhe: the proof of LAW stop_cut_notes_follow_the_cap
#
# PROOF: a note that is no length note starts the row as no note does (LR.str.cut_first); from j notes with m under the cap, the row is m notes, then the failure (LR.str.cut_climb, by induction on m).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_cut_notes_follow_the_cap(rc, k, row, other):
  match rc:
    case RnRecovery.RCfg{long, le, re, rp}:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Truncated{}, k, row), RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, 0n), LR.str.cut_first(k, row, long, le, re, rp, other)) : {StopRecover.climb(1n+long, RnRecovery.RCfg{long, le, re, rp}, RnDecision.Truncated{}, _) == StopRecover.ups(long, 0n, [RnDecision.Quits{}]) : List<&2, RnDecision.Help>}
      %LR.str.add_zero(long) : {StopRecover.climb(1n+long, RnRecovery.RCfg{_, le, re, rp}, RnDecision.Truncated{}, RnDecision.decide.recover(RnRecovery.RCfg{_, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, 0n)) == StopRecover.ups(long, 0n, [RnDecision.Quits{}]) : List<&2, RnDecision.Help>}
      LR.str.cut_climb(long, 0n, le, re, rp)
