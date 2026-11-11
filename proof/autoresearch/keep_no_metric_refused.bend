# eukhe: the proof of LAW keep_no_metric_refused

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/events.bend as AE

def knm.of(+c: ArS.Cfg, seg: Nat, mode: ArS.Mode, runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, desc: String, why: Maybe<&2, String>, devs: Nat, passed: {ArM.ar_fin(ArS.St{Some{c}, seg, mode, runs, pend}) == Some{True{}} : Maybe<&2, Bool>}, none: {AutoresearchEvents.ar_pmetric(ArS.St{Some{c}, seg, mode, runs, pend}) == None{} : Maybe<&2, ArD.Dec>}) -> {ArP.step(ArS.St{Some{c}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_no_metric(ArS.Cfg.metric(c))} : ArS.Res}:
  match pend:
    case None{}:
      AE.ev.none_some(Bool, {ArP.step(ArS.St{Some{c}, seg, mode, runs, None{}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_no_metric(ArS.Cfg.metric(c))} : ArS.Res}, True{}, passed)
    case Some{p}:
      match p:
        case ArS.Pend{id, kvs, fin}:
          match fin:
            case None{}:
              AE.ev.none_some(Bool, {ArP.step(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_no_metric(ArS.Cfg.metric(c))} : ArS.Res}, True{}, passed)
            case Some{b}:
              match b:
                case False{}:
                  AE.ev.ft({ArP.step(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{False{}}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_no_metric(ArS.Cfg.metric(c))} : ArS.Res}, passed)
                case True{}:
                  %Equal.sym(Maybe<&2, ArD.Dec>, ArS.lookup(kvs, ArS.Cfg.metric(c)), None{}, none) : {ArP.keep.metric(_, c, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc) == ArS.Refuse{ArP.t_no_metric(ArS.Cfg.metric(c))} : ArS.Res}
                  {==}

def AutoresearchEvents.keep_no_metric_refused(s, c, desc, why, devs, passed, cfg, none):
  match s:
    case ArS.St{cf, seg, mode, runs, pend}:
      match cf:
        case None{}:
          AE.ev.none_some(ArS.Cfg, {ArP.step(ArS.St{None{}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_no_metric(ArS.Cfg.metric(c))} : ArS.Res}, c, cfg)
        case Some{+c2}:
          %AE.ev.some_inj(ArS.Cfg, c2, c, cfg) : {ArP.step(ArS.St{Some{c2}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_no_metric(ArS.Cfg.metric(_))} : ArS.Res}
          knm.of(c2, seg, mode, runs, pend, desc, why, devs, passed, none)
