# eukhe: the proof of LAW crash_needs_failure

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/log.bend as AgLog

def Autoresearch.crash_needs_failure(s, desc, why, devs, s2, eff, stop, ok):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          AgLog.ag.refused({Autoresearch.ar_fin(ArS.St{cfg, seg, mode, runs, None{}}) == Some{False{}} : Maybe<&2, Bool>}, ArP.t_no_run(), s2, eff, stop, ok)
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case None{}:
                  AgLog.ag.refused({None{} == Some{False{}} : Maybe<&2, Bool>}, ArP.t_running(), s2, eff, stop, ok)
                case Some{passed}:
                  match passed:
                    case True{}:
                      AgLog.ag.refused({Some{True{}} == Some{False{}} : Maybe<&2, Bool>}, ArP.t_passed(), s2, eff, stop, ok)
                    case False{}:
                      {==}
