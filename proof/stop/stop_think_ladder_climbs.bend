# eukhe: the proof of LAW stop_think_ladder_climbs
#
# PROOF: a note that is no length note starts the ladder as no note does (LR.str.think_first); from j notes with m under the cap, the ladder is m notes, then its end (LR.str.climb_go, by induction on m).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/decision.bend as RnDecision
import ./base/recover.bend as LR
import ../../laws/stop/recover.bend as StopRecover

def StopRecover.stop_think_ladder_climbs(rc, w, c, p, o, lower, k, row, other):
  match rc:
    case RnRecovery.RCfg{long, le, re, rp}:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, k, row), RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, 0n), LR.str.think_first(k, row, long, le, re, rp, w, c, p, o, lower, other)) : {StopRecover.climb(1n+long, RnRecovery.RCfg{long, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, _) == StopRecover.ups(long, 0n, StopRecover.ladder_end(lower, long)) : List<&2, RnDecision.Help>}
      %LR.str.add_zero(long) : {StopRecover.climb(1n+long, RnRecovery.RCfg{_, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnDecision.decide.recover(RnRecovery.RCfg{_, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, 0n)) == StopRecover.ups(long, 0n, StopRecover.ladder_end(lower, _)) : List<&2, RnDecision.Help>}
      LR.str.climb_go(long, 0n, le, re, rp, w, c, p, o, lower)
