# eukhe: the proof of LAW stop_goes_never_answers
#
# PROOF: the walk's Goes{d} reads the reply of d's recovery, which retries (LS.sts.go); a reply that retries never answers the run (LS.sts.never).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../bend/stop.bend as S
import ./base/stand.bend as LS
import ../../laws/stop.bend as Stop

def Stop.stop_goes_never_answers(cfg, f, d, goes, rc, k, row, w, ca, pr, o, cu, lo, fin, got, r, c, a, n, p):
  %Equal.sym(S.Pick, S.walk(f), S.Goes{d}, goes) : {Stop.retried(Stop.stop_reply(_, f, rc, k, row, w, ca, pr, o, cu, lo)) == True{} : Bool} & {Stop.answered(RnState.St.ph(RnStep.step(cfg, RnState.St{RnState.Call{}, r, c, a, n, p}, RnState.Go{Stop.stop_reply(_, f, rc, k, row, w, ca, pr, o, cu, lo), fin, got}))) == False{} : Bool}
  +h = LS.sts.go(d, rc, k, row, w, ca, pr, o, cu, lo, RnState.Ended.reply(RnState.Ended{S.Facts.text(f), False{}}))
  (h, LS.sts.never(cfg, Stop.go_reply(d, rc, k, row, w, ca, pr, o, cu, lo, RnState.Ended.reply(RnState.Ended{S.Facts.text(f), False{}})), r, c, a, n, p, h))
