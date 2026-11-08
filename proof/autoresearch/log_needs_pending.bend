# eukhe: the proof of LAW log_needs_pending

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/log.bend as AgLog

def Autoresearch.log_needs_pending(s, st, desc, why, devs, no):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          {==}
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case None{}:
                  {==}
                case Some{passed}:
                  AgLog.ag.some_none({ArP.step(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{passed}}}}, ArS.Log{st, desc, why, devs}) == ArS.Refuse{Autoresearch.ar_log_refusal(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{passed}}}})} : ArS.Res}, passed, no)
