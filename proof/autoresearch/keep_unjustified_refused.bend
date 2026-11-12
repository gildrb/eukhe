# eukhe: the proof of LAW keep_unjustified_refused: the code's beats is
# the spec's all_beaten (AgLog.ag.beats_eq), its justification test the
# law's (AE.ev.just)

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../spec/autoresearch/segment.bend as SG
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/log.bend as AgLog
import ./base/events.bend as AE

def kur.of(+c: ArS.Cfg, +x: ArD.Dec, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, desc: String, +why: Maybe<&2, String>, +devs: Nat, passed: {ArM.ar_fin(ArS.St{Some{c}, seg, mode, runs, pend}) == Some{True{}} : Maybe<&2, Bool>}, got: {AutoresearchEvents.ar_pmetric(ArS.St{Some{c}, seg, mode, runs, pend}) == Some{x} : Maybe<&2, ArD.Dec>}, better: {ArS.beats(ArS.Cfg.dir(c), x, runs, seg) == True{} : Bool}, left: {Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)) == False{} : Bool}) -> {ArP.step(ArS.St{Some{c}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_justify()} : ArS.Res}:
  match pend:
    case None{}:
      AE.ev.none_some(Bool, {ArP.step(ArS.St{Some{c}, seg, mode, runs, None{}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_justify()} : ArS.Res}, True{}, passed)
    case Some{p}:
      match p:
        case ArS.Pend{id, kvs, fin}:
          match fin:
            case None{}:
              AE.ev.none_some(Bool, {ArP.step(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_justify()} : ArS.Res}, True{}, passed)
            case Some{b}:
              match b:
                case False{}:
                  AE.ev.ft({ArP.step(ArS.St{Some{c}, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{False{}}}}}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_justify()} : ArS.Res}, passed)
                case True{}:
                  %Equal.sym(Maybe<&2, ArD.Dec>, ArS.lookup(kvs, ArS.Cfg.metric(c)), Some{x}, got) : {ArP.keep.metric(_, c, why, devs, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc) == ArS.Refuse{ArP.t_justify()} : ArS.Res}
                  %Equal.sym(Bool, ArS.beats(ArS.Cfg.dir(c), x, runs, seg), True{}, better) : {ArP.keep.beats(_, x, ArS.Cfg.dir(c), why, devs, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc) == ArS.Refuse{ArP.t_justify()} : ArS.Res}
                  %Equal.sym(Bool, Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), False{}, left) : {ArP.keep.why(_, Some{c}, seg, mode, runs, ArS.Pend{id, kvs, Some{True{}}}, desc) == ArS.Refuse{ArP.t_justify()} : ArS.Res}
                  {==}

def AutoresearchEvents.keep_unjustified_refused(s, c, x, desc, why, devs, passed, cfg, got, better, left):
  match s:
    case ArS.St{cf, +seg, mode, +runs, pend}:
      match cf:
        case None{}:
          AE.ev.none_some(ArS.Cfg, {ArP.step(ArS.St{None{}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, desc, why, devs}) == ArS.Refuse{ArP.t_justify()} : ArS.Res}, c, cfg)
        case Some{+c2}:
          +hc = AE.ev.some_inj(ArS.Cfg, c2, c, cfg)
          +l2 = Equal.trans(Bool, Bool.or(Nat.is_eq(devs, 0n), ArP.justified(why)), Bool.or(Nat.is_eq(devs, 0n), ArM.ar_justified(why)), False{}, Equal.cong(Bool, Bool, j => Bool.or(Nat.is_eq(devs, 0n), j), ArP.justified(why), ArM.ar_justified(why), AE.ev.just(why)), left)
          +b2 = Equal.trans(Bool, ArS.beats(ArS.Cfg.dir(c2), x, runs, seg), SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(c2), x, runs, seg), True{}, AgLog.ag.beats_eq(ArS.Cfg.dir(c2), x, runs, seg), Equal.trans(Bool, SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(c2), x, runs, seg), SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(c), x, runs, seg), True{}, Equal.cong(ArS.Cfg, Bool, k => SG.all_beaten(~ArD.Dec.cmp, ArS.Cfg.dir(k), x, runs, seg), c2, c, hc), better))
          kur.of(c2, x, seg, mode, runs, pend, desc, why, devs, passed, got, b2, l2)
