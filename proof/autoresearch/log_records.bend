# eukhe: the proof of LAW log_records

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/log.bend as AgLog

def Autoresearch.log_records(s, st, desc, why, devs, s2, eff, stop, ok):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          AgLog.ag.refused(Empty, ArP.t_no_run(), s2, eff, stop, ok)
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case None{}:
                  AgLog.ag.refused(Autoresearch.ar_logged(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, st, desc, s2), ArP.t_running(), s2, eff, stop, ok)
                case Some{+passed}:
                  match st:
                    case ArS.Keep{}:
                      AgLog.ag.keep_done(passed, cfg, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, desc, s2, eff, stop, ok)
                    case ArS.Discard{}:
                      AgLog.ag.done(cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Discard{}, desc, ArS.Reset{}, s2, eff, stop, ok)
                    case ArS.Crash{}:
                      AgLog.ag.need_done(Bool.not(passed), ArP.t_passed(), cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Crash{}, desc, s2, eff, stop, ok)
                    case ArS.Checks{}:
                      AgLog.ag.need_done(passed, ArP.t_failed(), cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Checks{}, desc, s2, eff, stop, ok)
