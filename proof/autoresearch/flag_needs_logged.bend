# eukhe: the proof of LAW flag_needs_logged: the code's walk finds a run
# exactly when a logged row has its id (FL.fl.found)

import Base
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../spec/autoresearch/metric_line.bend as SL
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/log.bend as AgLog
import ./base/events.bend as AE
import ./base/flag.bend as FL

def fnl.found(q: List<&2, ArS.Row> & Bool, +n: Nat, cfg: Maybe<&2, ArS.Cfg>, seg: Nat, mode: ArS.Mode, pend: Maybe<&2, ArS.Pend>, h: {AE.ev.snd(q) == False{} : Bool}) -> {ArP.flag.found(q, n, cfg, seg, mode, pend) == ArS.Refuse{ArP.t_not_logged(n)} : ArS.Res}:
  match q:
    case (a, f):
      match f:
        case True{}:
          AS.as.absurd_tf({ArP.flag.found((a, True{}), n, cfg, seg, mode, pend) == ArS.Refuse{ArP.t_not_logged(n)} : ArS.Res}, h)
        case False{}:
          {==}

def fnl.of(s: ArS.St, +n: Nat, no: {ArM.ar_logged_id(ArM.ar_runs(s), n) == False{} : Bool}) -> {ArP.flag.reason(True{}, s, n) == ArS.Refuse{ArP.t_not_logged(n)} : ArS.Res}:
  match s:
    case ArS.St{cfg, seg, mode, +runs, pend}:
      fnl.found(ArP.flag.rows(runs, n), n, cfg, seg, mode, pend, Equal.trans(Bool, AE.ev.snd(ArP.flag.rows(runs, n)), ArM.ar_logged_id(runs, n), False{}, FL.fl.found(runs, n), no))

def AutoresearchEvents.flag_needs_logged(s, n, reason, some, no):
  +e = Equal.trans(Bool, ArL.some(reason), SL.nonempty(reason), True{}, AgLog.ag.some_eq(reason), some)
  %Equal.sym(Bool, ArL.some(reason), True{}, e) : {ArP.flag.reason(_, s, n) == ArS.Refuse{ArP.t_not_logged(n)} : ArS.Res}
  fnl.of(s, n, no)
