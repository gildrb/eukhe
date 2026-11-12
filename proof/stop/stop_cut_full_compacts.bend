# eukhe: the proof of LAW stop_cut_full_compacts
#
# PROOF: the model's window test is the spec's, so the stop is full (LC.stc.full): the window is spent and a compaction can run (LA.stb.and_l, LA.stb.and_r), so the walk's LengthStop continues it, and the ladder, reading the same window, compacts (LC.stc.compacts); the reply is the cut overflow, whose step computes.

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../bend/stop.bend as S
import ./base.bend as LA
import ./base/cut.bend as LC
import ../../laws/stop.bend as Stop
import ../../laws/stop/cut.bend as StopCut

def StopCut.stop_cut_full_compacts(cfg, b, p, rc, k, row, w, ca, pr, o, cu, lo, full, r, c, a, n, pl):
  +e = LC.stc.full(w, ca, pr, o, cu, full)
  +hc = LA.stb.and_l(cu, RnRecovery.bound(w, ca, pr, o), e)
  +hb = LA.stb.and_r(cu, RnRecovery.bound(w, ca, pr, o), e)
  %Equal.sym(Bool, RnRecovery.bound(w, ca, pr, o), True{}, hb) : {RnStep.call(cfg, Stop.stop_reply(S.walk(S.Facts{True{}, True{}, b, p, _, cu}), S.Facts{True{}, True{}, b, p, _, cu}, rc, k, row, w, ca, pr, o, cu, lo), r, 1n+c, a, n, pl) == RnState.St{RnState.Compact{True{}}, r, c, a, n, pl} : RnState.St}
  %Equal.sym(Bool, cu, True{}, hc) : {RnStep.call(cfg, Stop.stop_reply(S.walk(S.Facts{True{}, True{}, b, p, True{}, _}), S.Facts{True{}, True{}, b, p, True{}, _}, rc, k, row, w, ca, pr, o, cu, lo), r, 1n+c, a, n, pl) == RnState.St{RnState.Compact{True{}}, r, c, a, n, pl} : RnState.St}
  %Equal.sym(RnDecision.Help, RnDecision.decide.recover(rc, RnDecision.Thought{w, ca, pr, o, cu, lo}, k, row), RnDecision.Compacts{}, LC.stc.compacts(rc, k, row, w, ca, pr, o, cu, lo, e)) : {RnStep.call(cfg, Stop.help_reply(_, True{}, RnState.Ended.reply(RnState.Ended{True{}, False{}})), r, 1n+c, a, n, pl) == RnState.St{RnState.Compact{True{}}, r, c, a, n, pl} : RnState.St}
  {==}
