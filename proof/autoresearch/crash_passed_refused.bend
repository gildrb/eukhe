# eukhe: the proof of LAW crash_passed_refused

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/events.bend as AE

def AutoresearchEvents.crash_passed_refused(s, desc, why, devs, passed):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          AE.ev.none_some(Bool, {ArP.step(ArS.St{cfg, seg, mode, runs, None{}}, ArS.Log{ArS.Crash{}, desc, why, devs}) == ArS.Refuse{ArP.t_passed()} : ArS.Res}, True{}, passed)
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case None{}:
                  AE.ev.none_some(Bool, {ArP.step(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Log{ArS.Crash{}, desc, why, devs}) == ArS.Refuse{ArP.t_passed()} : ArS.Res}, True{}, passed)
                case Some{b}:
                  match b:
                    case True{}:
                      {==}
                    case False{}:
                      AE.ev.ft({ArP.step(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{False{}}}}}, ArS.Log{ArS.Crash{}, desc, why, devs}) == ArS.Refuse{ArP.t_passed()} : ArS.Res}, passed)
