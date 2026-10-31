# eukhe: the proof of LAW log_accepted

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/accept.bend as AaAccept

def Autoresearch.log_accepted(s, st, desc, why, devs, ok):
  match s:
    case ArS.St{+cfg, +seg, mode, +runs, pend}:
      match pend:
        case None{}:
          AaAccept.aa.absurd(Empty, ok)
        case Some{p}:
          match p:
            case ArS.Pend{+id, +kvs, f}:
              match f:
                case None{}:
                  AaAccept.aa.absurd(Empty, ok)
                case Some{+passed}:
                  match st:
                    case ArS.Keep{}:
                      AaAccept.aa.absurd(Autoresearch.ar_accepts(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{passed}}}}, ArS.Keep{}, desc, ArP.step(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{passed}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}), ArS.Reset{}), ok)
                    case ArS.Discard{}:
                      AaAccept.aa.done(cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Discard{}, desc, ArS.Reset{})
                    case ArS.Crash{}:
                      AaAccept.aa.need(Bool.not(passed), ok, ArP.t_passed(), cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Crash{}, desc)
                    case ArS.Checks{}:
                      AaAccept.aa.need(passed, ok, ArP.t_failed(), cfg, seg, mode, runs, ArS.Pend{id, kvs, Some{passed}}, ArS.Checks{}, desc)
