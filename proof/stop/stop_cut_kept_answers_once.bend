# eukhe: the proof of LAW stop_cut_kept_answers_once
#
# PROOF: the model's window test is the spec's, so the stop is not full (LC.stc.room); the walk lets it stand and the run reads it as Plain (LC.stc.kept), which answers the run; an answered run stays so, counts no further answer and sends no request (LS.sts.stays, LS.sts.none, LS.sts.plain).

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../bend/stop.bend as S
import ./base/cut.bend as LC
import ./base/stand.bend as LS
import ../../laws/stop.bend as Stop
import ../../laws/stop/cut.bend as StopCut

def StopCut.stop_cut_kept_answers_once(cfg, b, p, rc, k, row, w, ca, pr, o, cu, lo, room, fin, got, r, c, a, n, pl, more, t):
  %Equal.sym(RnState.Reply, StopCut.cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, cu, lo), RnState.Plain{}, LC.stc.kept(RnRecovery.full(w, ca, pr, o, cu), b, p, rc, k, row, w, ca, pr, o, cu, lo, LC.stc.room(w, ca, pr, o, cu, room))) : {RnStep.run.go(RnState.Go{_, fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}) == RnState.St{RnState.Answered{}, r, c, a, n, pl} : RnState.St} & {Stop.answers.go(RnState.Go{_, fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}) == 1n : Nat} & {RnRequest.reqs.go(RnState.Go{_, fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}, t) == t : RnRequest.Reqs}
  (LS.sts.stays(more, cfg, r, c, a, n, pl), (Equal.cong(Nat, Nat, x => 1n+x, Stop.answers.go(more, cfg, RnState.St{RnState.Answered{}, r, c, a, n, pl}), 0n, LS.sts.none(more, cfg, r, c, a, n, pl)), LS.sts.plain(more, cfg, r, c, a, n, pl, fin, got, t)))
