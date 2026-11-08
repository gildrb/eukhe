# eukhe: the proof of LAW stop_stand_sends_no_request
#
# PROOF: the walk's Stands and the text read the reply as Plain, which changes no request; an answered run sends none.

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../bend/stop.bend as S
import ./base/stand.bend as LS
import ../../laws/stop.bend as Stop

# an answer at a reply sends, cuts and notes no request, nor does any
# input after it
def stop_stand_sends_no_request.plain(more: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, -fin: RnState.Fin, -got: RnState.Got, t: RnRequest.Reqs) -> {RnRequest.reqs.go(RnState.Go{RnState.Plain{}, fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}, t) == t : RnRequest.Reqs}:
  match t:
    case RnRequest.Reqs{ctx, k, note, log}:
      LS.sts.kept(more, cfg, r, c, a, n, p, RnRequest.Reqs{ctx, k, note, log})

def Stop.stop_stand_sends_no_request(cfg, f, stands, said, rc, k, row, w, ca, pr, o, cu, lo, fin, got, r, c, a, n, p, more, t):
  %Equal.sym(S.Pick, S.walk(f), S.Stands{}, stands) : {RnRequest.reqs.go(RnState.Go{Stop.stop_reply(_, f, rc, k, row, w, ca, pr, o, cu, lo), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}, t) == t : RnRequest.Reqs}
  %Equal.sym(Bool, S.Facts.text(f), True{}, said) : {RnRequest.reqs.go(RnState.Go{RnState.Ended.reply(RnState.Ended{_, False{}}), fin, got} <> more, cfg, RnState.St{RnState.Call{}, r, c, a, n, p}, t) == t : RnRequest.Reqs}
  stop_stand_sends_no_request.plain(more, cfg, r, c, a, n, p, fin, got, t)
