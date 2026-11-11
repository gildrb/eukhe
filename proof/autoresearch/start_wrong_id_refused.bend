# eukhe: the proof of LAW start_wrong_id_refused: the starts the history
# accepted are the code's count of started runs (ST.st.k), and a start of
# another id than one past it is refused

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/history.bend as ArH
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/starts.bend as ST

def swr.of(s: ArS.St, +n: Nat, has: {ArM.ar_no_cfg(s) == False{} : Bool}, ne: {Nat.is_eq(n, 1n+ArS.St.started(s)) == False{} : Bool}) -> {ArP.step(s, ArS.Begin{n}) == ArS.Refuse{String.append("autoresearch.run: the next run is ", Nat.show(1n+ArS.St.started(s)))} : ArS.Res}:
  match s:
    case ArS.St{cfg, seg, mode, +runs, +pend}:
      match cfg:
        case None{}:
          AS.as.absurd_tf({ArP.step(ArS.St{None{}, seg, mode, runs, pend}, ArS.Begin{n}) == ArS.Refuse{String.append("autoresearch.run: the next run is ", Nat.show(1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))))} : ArS.Res}, has)
        case Some{c}:
          %Equal.sym(Bool, Nat.is_eq(n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))), False{}, ne) : {ArP.begin.at(_, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), c, seg, mode, runs, pend) == ArS.Refuse{String.append("autoresearch.run: the next run is ", Nat.show(1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))))} : ArS.Res}
          {==}

def AutoresearchEvents.start_wrong_id_refused(evs, n, has, ne):
  +k = ST.st.k(evs)
  +ne2 = Equal.trans(Bool, Nat.is_eq(n, 1n+ArS.St.started(ArM.ar_run(evs))), Nat.is_eq(n, 1n+ArH.ar_starts(evs)), False{}, Equal.cong(Nat, Bool, x => Nat.is_eq(n, 1n+x), ArS.St.started(ArM.ar_run(evs)), ArH.ar_starts(evs), k), ne)
  %k : {ArP.step(ArM.ar_run(evs), ArS.Begin{n}) == ArS.Refuse{String.append("autoresearch.run: the next run is ", Nat.show(1n+_))} : ArS.Res}
  swr.of(ArM.ar_run(evs), n, has, ne2)
