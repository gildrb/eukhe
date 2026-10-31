# eukhe: the proof of LAW output_needs_run

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def Autoresearch.output_needs_run(s, t, neg, code, timeout, idle):
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      match pend:
        case None{}:
          {==}
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case None{}:
                  AS.as.absurd_tf({[ArP.step(ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Line{t}), ArP.step(ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Finish{neg, code, timeout})] == [ArS.Refuse{"autoresearch: no run is in progress"}, ArS.Refuse{"autoresearch: no run is in progress"}] : List<&2, ArS.Res>}, idle)
                case Some{b}:
                  {==}
