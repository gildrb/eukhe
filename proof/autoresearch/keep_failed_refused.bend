# eukhe: the proof of LAW keep_failed_refused

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/events.bend as AE

def AutoresearchEvents.keep_failed_refused(s, desc, why, devs, failed):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          AE.ev.none_some(Bool, {ArP.step(ArS.St{cfg, seg, mode, runs, None{}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_failed_keep()} : ArS.Res}, False{}, failed)
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case None{}:
                  AE.ev.none_some(Bool, {ArP.step(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_failed_keep()} : ArS.Res}, False{}, failed)
                case Some{b}:
                  match b:
                    case True{}:
                      AE.ev.tf({ArP.step(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{True{}}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_failed_keep()} : ArS.Res}, failed)
                    case False{}:
                      {==}
