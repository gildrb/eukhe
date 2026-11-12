# eukhe: the proof of LAW start_accepted: the starts the history accepted
# are the code's count of started runs (ST.st.k); the start one past it
# is accepted, and its rows are the old ones and the abandoned pending run
# (AE.ev.abandons)

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/history.bend as ArH
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/history.bend as AH
import ./base/events.bend as AE
import ./base/starts.bend as ST

def sac.of(s: ArS.St, has: {ArM.ar_no_cfg(s) == False{} : Bool}) -> AutoresearchEvents.ar_start_ok(s, 1n+ArS.St.started(s), ArP.step(s, ArS.Begin{1n+ArS.St.started(s)})):
  match s:
    case ArS.St{cfg, +seg, +mode, +runs, +pend}:
      match cfg:
        case None{}:
          AS.as.absurd_tf(AutoresearchEvents.ar_start_ok(ArS.St{None{}, seg, mode, runs, pend}, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), ArP.step(ArS.St{None{}, seg, mode, runs, pend}, ArS.Begin{1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))})), has)
        case Some{+c}:
          +k = {1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)) : Nat}
          %Equal.sym(Bool, Nat.is_eq(k, k), True{}, AH.ah.eq_refl(k)) : AutoresearchEvents.ar_start_ok(ArS.St{Some{c}, seg, mode, runs, pend}, k, ArP.begin.at(_, k, c, seg, mode, runs, pend))
          ({==}, ({==}, AE.ev.abandons(Some{c}, seg, mode, runs, pend, ArS.Cfg.metric(c))))

def AutoresearchEvents.start_accepted(evs, has):
  %ST.st.k(evs) : AutoresearchEvents.ar_start_ok(ArM.ar_run(evs), 1n+_, ArP.step(ArM.ar_run(evs), ArS.Begin{1n+_}))
  sac.of(ArM.ar_run(evs), has)
