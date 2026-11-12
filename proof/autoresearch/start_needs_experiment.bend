# eukhe: the proof of LAW start_needs_experiment

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS

def AutoresearchEvents.start_needs_experiment(s, n, no):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match cfg:
        case None{}:
          {==}
        case Some{c}:
          AS.as.absurd({ArP.step(ArS.St{Some{c}, seg, mode, runs, pend}, ArS.Begin{n}) == ArS.Refuse{ArP.t_no_cfg()} : ArS.Res}, no)
