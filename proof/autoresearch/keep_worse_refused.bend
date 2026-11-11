# eukhe: the proof of LAW keep_worse_refused: the code's beats is the
# spec's all_beaten (AgLog.ag.beats_eq); the code's texts of the best and
# the direction are the law's (AE.ev.best_text, AE.ev.dir_word)

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../spec/autoresearch/segment.bend as SG
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/log.bend as AgLog
import ./base/events.bend as AE

def kwr.text(+x: ArD.Dec, +b: Maybe<&2, ArD.Dec>, +d: ArS.Dir) -> String:
  String.append("autoresearch.log: ", String.append(ArD.show(x), String.append(" is not better than the best kept ", String.append(AutoresearchEvents.ar_best_text(b), String.append(" (", String.append(AutoresearchEvents.ar_dir_word(d), " is better); log discard"))))))

def kwr.t(+x: ArD.Dec, +b: Maybe<&2, ArD.Dec>, +d: ArS.Dir) -> {ArS.Refuse{ArP.t_worse(x, b, d)} == ArS.Refuse{kwr.text(x, b, d)} : ArS.Res}:
  %AE.ev.best_text(b) : {ArS.Refuse{ArP.t_worse(x, b, d)} == ArS.Refuse{String.append("autoresearch.log: ", String.append(ArD.show(x), String.append(" is not better than the best kept ", String.append(_, String.append(" (", String.append(AutoresearchEvents.ar_dir_word(d), " is better); log discard"))))))} : ArS.Res}
  %AE.ev.dir_word(d) : {ArS.Refuse{ArP.t_worse(x, b, d)} == ArS.Refuse{String.append("autoresearch.log: ", String.append(ArD.show(x), String.append(" is not better than the best kept ", String.append(ArP.t_best(b), String.append(" (", String.append(_, " is better); log discard"))))))} : ArS.Res}
  {==}

def kwr.of(+c: ArS.Cfg, +x: ArD.Dec, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, desc: String, why: Maybe<&2, String>, devs: Nat, passed: {ArM.ar_fin(ArS.St{Some{c}, seg, mode, runs, pend}) == Some{True{}} : Maybe<&2, Bool>}, got: {AutoresearchEvents.ar_pmetric(ArS.St{Some{c}, seg, mode, runs, pend}) == Some{x} : Maybe<&2, ArD.Dec>}, worse: {ArS.beats(ArS.Cfg.dir(c), x, runs, seg) == False{} : Bool}) -> {ArP.step(ArS.St{Some{c}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{kwr.text(x, ArS.last(runs, seg), ArS.Cfg.dir(c))} : ArS.Res}:
  match pend:
    case None{}:
      AE.ev.none_some(Bool, {ArP.step(ArS.St{Some{c}, seg, mode, runs, None{}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{kwr.text(x, ArS.last(runs, seg), ArS.Cfg.dir(c))} : ArS.Res}, True{}, passed)
    case Some{p}:
      match p:
        case ArS.Pend{id, kvs, fin}:
          match fin:
            case None{}:
              AE.ev.none_some(Bool, {ArP.step(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{kwr.text(x, ArS.last(runs, seg), ArS.Cfg.dir(c))} : ArS.Res}, True{}, passed)
            case Some{b}:
              match b:
                case False{}:
                  AE.ev.ft({ArP.step(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{False{}}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{kwr.text(x, ArS.last(runs, seg), ArS.Cfg.dir(c))} : ArS.Res}, passed)
                case True{}:
                  %Equal.sym(Maybe<&2, ArD.Dec>, ArS.lookup(kvs, ArS.Cfg.metric(c)), Some{x}, got) : {ArP.keep.metric(_, c, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc) == ArS.Refuse{kwr.text(x, ArS.last(runs, seg), ArS.Cfg.dir(c))} : ArS.Res}
                  %Equal.sym(Bool, ArS.beats(ArS.Cfg.dir(c), x, runs, seg), False{}, worse) : {ArP.keep.beats(_, x, ArS.Cfg.dir(c), why, devs, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc) == ArS.Refuse{kwr.text(x, ArS.last(runs, seg), ArS.Cfg.dir(c))} : ArS.Res}
                  kwr.t(x, ArS.last(runs, seg), ArS.Cfg.dir(c))

def AutoresearchEvents.keep_worse_refused(s, c, x, desc, why, devs, passed, cfg, got, worse):
  match s:
    case ArS.St{cf, +seg, mode, +runs, pend}:
      match cf:
        case None{}:
          AE.ev.none_some(ArS.Cfg, {ArP.step(ArS.St{None{}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{kwr.text(x, ArS.last(runs, seg), ArS.Cfg.dir(c))} : ArS.Res}, c, cfg)
        case Some{+c2}:
          +hc = AE.ev.some_inj(ArS.Cfg, c2, c, cfg)
          +w2 = Equal.trans(Bool, ArS.beats(ArS.Cfg.dir(c2), x, runs, seg), SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(c2), x, runs, seg), False{}, AgLog.ag.beats_eq(ArS.Cfg.dir(c2), x, runs, seg), Equal.trans(Bool, SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(c2), x, runs, seg), SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(c), x, runs, seg), False{}, Equal.cong(ArS.Cfg, Bool, k => SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(k), x, runs, seg), c2, c, hc), worse))
          %hc : {ArP.step(ArS.St{Some{c2}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{kwr.text(x, ArS.last(runs, seg), ArS.Cfg.dir(_))} : ArS.Res}
          kwr.of(c2, x, seg, mode, runs, pend, desc, why, devs, passed, got, w2)
