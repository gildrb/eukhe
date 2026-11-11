# eukhe: the proof of LAW flag_accepted: the code's walk finds the
# logged run (FL.fl.found), changes no row but for flags (FL.fl.unmark)
# and no other run's flag (FL.fl.other)

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

def fac.Others(a: List<&2, ArS.Row>, +runs: List<&2, ArS.Row>, +n: Nat) -> Type:
  @k: Nat -> {Nat.is_eq(n, k) == False{} : Bool} -> {ArM.ar_flagged(a, k) == ArM.ar_flagged(runs, k) : Bool}

def fac.found(q: List<&2, ArS.Row> & Bool, +n: Nat, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, hf: {AE.ev.snd(q) == True{} : Bool}, hu: {AutoresearchEvents.ar_unmark(AE.ev.fst(q)) == AutoresearchEvents.ar_unmark(runs) : List<&2, ArS.Row>}, ho: fac.Others(AE.ev.fst(q), runs, n)) -> AutoresearchEvents.ar_flag_ok(ArS.St{cfg, seg, mode, runs, pend}, n, ArP.flag.found(q, n, cfg, seg, mode, pend)):
  match q:
    case (a, f):
      match f:
        case True{}:
          ({==}, ({==}, ({==}, (hu, ho))))
        case False{}:
          AS.as.absurd(AutoresearchEvents.ar_flag_ok(ArS.St{cfg, seg, mode, runs, pend}, n, ArP.flag.found((a, False{}), n, cfg, seg, mode, pend)), hf)

def fac.of(s: ArS.St, +n: Nat, yes: {ArM.ar_logged_id(ArM.ar_runs(s), n) == True{} : Bool}) -> AutoresearchEvents.ar_flag_ok(s, n, ArP.flag.reason(True{}, s, n)):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, +pend}:
      fac.found(ArP.flag.rows(runs, n), n, cfg, seg, mode, runs, pend, Equal.trans(Bool, AE.ev.snd(ArP.flag.rows(runs, n)), ArM.ar_logged_id(runs, n), True{}, FL.fl.found(runs, n), yes), FL.fl.unmark(runs, n), k => ne => FL.fl.other(runs, n, k, ne))

def AutoresearchEvents.flag_accepted(s, n, reason, some, yes):
  +e = Equal.trans(Bool, ArL.some(reason), SL.nonempty(reason), True{}, AgLog.ag.some_eq(reason), some)
  %Equal.sym(Bool, ArL.some(reason), True{}, e) : AutoresearchEvents.ar_flag_ok(s, n, ArP.flag.reason(_, s, n))
  fac.of(s, n, yes)
