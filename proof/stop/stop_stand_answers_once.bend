# eukhe: the proof of LAW stop_stand_answers_once
#
# PROOF: the walk's Stands and the text read the reply as Plain, which answers the run; an answered run stays so and counts no further answer.

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../bend/stop.bend as S
import ./base/stand.bend as LS
import ../../laws/stop.bend as Stop

def Stop.stop_stand_answers_once(cfg, f, stands, said, rc, k, row, w, ca, pr, o, cu, lo, fin, got, r, c, a, n, p, more):
  %Equal.sym(S.Pick, S.walk(f), S.Stands{}, stands) : {RnStep.run.go(RnState.Go{Stop.stop_reply(_, f, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}) == RnState.St{RnState.Answered{}, r, c, a, n, p} : RnState.St} & {Stop.answers.go(RnState.Go{Stop.stop_reply(_, f, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}) == 1n : Nat}
  %Equal.sym(Bool, S.Facts.text(f), True{}, said) : {RnStep.run.go(RnState.Go{RnState.Ended.reply(RnState.Ended{_, False{}}), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}) == RnState.St{RnState.Answered{}, r, c, a, n, p} : RnState.St} & {Stop.answers.go(RnState.Go{RnState.Ended.reply(RnState.Ended{_, False{}}), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}) == 1n : Nat}
  (LS.sts.stays(more, cfg, r, c, a, n, p), Equal.cong(Nat, Nat, x => 1n+x, Stop.answers.go(more, cfg, RnState.St{RnState.Answered{}, r, c, a, n, p}), 0n, LS.sts.none(more, cfg, r, c, a, n, p)))
