# eukhe: the proof of LAW keep_is_better

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/log.bend as AgLog

def Autoresearch.keep_is_better(s, desc, why, devs, s2, eff, stop, ok):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          AgLog.ag.refused(Autoresearch.ar_keep_beats(ArS.St{cfg, seg, mode, runs, None{}}), ArP.t_no_run(), s2, eff, stop, ok)
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case None{}:
                  AgLog.ag.refused(Autoresearch.ar_keep_beats(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}), ArP.t_running(), s2, eff, stop, ok)
                case Some{+passed}:
                  AgLog.ag.cfg_better(cfg, why, devs, seg, mode, runs, id, kvs, Some{passed}, desc, s2, eff, stop, AgLog.ag.keep_cfg(passed, cfg, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, desc, s2, eff, stop, ok))
