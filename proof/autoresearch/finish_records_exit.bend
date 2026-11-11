# eukhe: the proof of LAW finish_records_exit: the code's exit test is
# the law's (AE.ev.exit)

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/events.bend as AE

def AutoresearchEvents.finish_records_exit(s, neg, code, timeout, run):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          AS.as.absurd(AutoresearchEvents.ar_finish_ok(ArS.St{cfg, seg, mode, runs, None{}}, AutoresearchEvents.ar_exit_passed(neg, code, timeout), ArP.step(ArS.St{cfg, seg, mode, runs, None{}}, ArS.Finish{neg, code, timeout})), run)
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case Some{b}:
                  AS.as.absurd(AutoresearchEvents.ar_finish_ok(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{b}}}}, AutoresearchEvents.ar_exit_passed(neg, code, timeout), ArP.step(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{b}}}}, ArS.Finish{neg, code, timeout})), run)
                case None{}:
                  ({==}, ({==}, ({==}, ({==}, Equal.cong(Bool, Maybe<&2, Bool>, x => Some{x}, ArP.ok_exit(neg, code, timeout), AutoresearchEvents.ar_exit_passed(neg, code, timeout), AE.ev.exit(neg, code, timeout))))))
