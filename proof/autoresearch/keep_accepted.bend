# eukhe: the proof of LAW keep_accepted

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/accept.bend as AaAccept

def Autoresearch.keep_accepted(s, desc, why, devs, fin, beats, just):
  match s:
    case ArS.St{cfg, +seg, mode, +runs, pend}:
      match cfg:
        case None{}:
          match beats:
        case Some{+c}:
          match pend:
            case None{}:
              AaAccept.aa.none_some(Empty, True{}, fin)
            case Some{p}:
              match p:
                case ArS.Pend{+id, +kvs, f}:
                  match f:
                    case None{}:
                      AaAccept.aa.none_some(Empty, True{}, fin)
                    case Some{passed}:
                      match passed:
                        case False{}:
                          AaAccept.aa.failed(Empty, fin)
                        case True{}:
                          AaAccept.aa.metric(ArS.lookup(kvs, ArS.Cfg.metric(c)), c, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc, beats, AaAccept.aa.just(devs, why, just))
