# eukhe: the proof of LAW stop_cut_dropped_ends_the_run
#
# PROOF: the model's window test is the spec's, so the window is spent (LC.stc.spent); with no compaction to make the walk drops the reply (LC.stc.drops) and the run reads it as Plain (LC.stc.dropped), which ends the run; an ended run stays so and sends no request (LS.sts.stays, LS.sts.plain).

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

# the run reads the dropped reply as its end and sends no further request
def scd.ends(+cfg: RnState.Cfg, -b: Bool, -p: Bool, -rc: RnRecovery.RCfg, -k: RnRecovery.Rk, -row: Nat, +w: Nat, +ca: Nat, +pr: Nat, +o: Nat, -lo: Bool, spent: {RnRecovery.bound(w, ca, pr, o) == True{} : Bool}, -fin: RnState.Fin, -got: RnState.Got, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +pl: Nat, +more: List<&2, RnState.Ev>, t: RnRequest.Reqs) -> {RnStep.run.go(RnState.Go{StopCut.cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, False{}, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}) == RnState.St{RnState.Answered{}, r, c, a, n, pl} : RnState.St} & {RnRequest.reqs.go(RnState.Go{StopCut.cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, False{}, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}, t) == t : RnRequest.Reqs}:
  %Equal.sym(RnState.Reply, StopCut.cut_reply(True{}, b, p, rc, k, row, w, ca, pr, o, False{}, lo), RnState.Plain{}, LC.stc.dropped(RnRecovery.bound(w, ca, pr, o), b, p, rc, k, row, w, ca, pr, o, lo, spent)) : {RnStep.run.go(RnState.Go{_, fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}) == RnState.St{RnState.Answered{}, r, c, a, n, pl} : RnState.St} & {RnRequest.reqs.go(RnState.Go{_, fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, pl}, t) == t : RnRequest.Reqs}
  (LS.sts.stays(more, cfg, r, c, a, n, pl), LS.sts.plain(more, cfg, r, c, a, n, pl, fin, got, t))

def StopCut.stop_cut_dropped_ends_the_run(cfg, b, p, rc, k, row, w, ca, pr, o, lo, spent, fin, got, r, c, a, n, pl, more, t):
  +e = LC.stc.spent(w, ca, pr, o, spent)
  (LC.stc.drops(RnRecovery.bound(w, ca, pr, o), b, p, e), scd.ends(cfg, b, p, rc, k, row, w, ca, pr, o, lo, e, fin, got, r, c, a, n, pl, more, t))
