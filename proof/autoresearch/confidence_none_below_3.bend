# eukhe: the proof of LAW confidence_none_below_3

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/log.bend as AgLog

def Autoresearch.confidence_none_below_3(s, few):
  match s:
    case ArS.St{c, +seg, mode, +runs, pend}:
      AgLog.ag.none_lt(ArT.dlen(ArT.vals(runs, seg)), ArS.first(runs, seg), ArS.last(runs, seg), ArT.vals(runs, seg), AgLog.ag.few(ArT.dlen(ArT.vals(runs, seg)), Autoresearch.ar_counted(runs, seg), AgLog.ag.cnt(runs, seg), few))
