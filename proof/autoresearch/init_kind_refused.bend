# eukhe: the proof of LAW init_kind_refused: the configuration has no
# error (AE.ev.err_none); on the same segment the code's same kind is the
# law's (AE.ev.same), which fails

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/events.bend as AE

def ikr.old(old: Maybe<&2, ArS.Cfg>, +c: ArS.Cfg, harness: Bool, seg: Nat, -mode: ArS.Mode, runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, kind: {AutoresearchEvents.ar_kind_ok(ArS.St{old, seg, mode, runs, pend}, False{}, c) == False{} : Bool}) -> {ArP.init.old(old, c, False{}, harness, seg, runs, pend) == ArS.Refuse{ArP.t_same()} : ArS.Res}:
  match old:
    case None{}:
      AS.as.absurd_tf({ArP.init.old(None{}, c, False{}, harness, seg, runs, pend) == ArS.Refuse{ArP.t_same()} : ArS.Res}, kind)
    case Some{+o}:
      +e = Equal.trans(Bool, ArP.same(o, c), Bool.and(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), ArM.ar_dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c))), False{}, AE.ev.same(o, c), kind)
      %Equal.sym(Bool, ArP.same(o, c), False{}, e) : {ArP.init.keep(_, c, ArS.Cfg.metric(o), seg, runs, pend) == ArS.Refuse{ArP.t_same()} : ArS.Res}
      {==}

def AutoresearchEvents.init_kind_refused(s, c, harness, name, cap, kind):
  match s:
    case ArS.St{old, seg, mode, runs, pend}:
      %Equal.sym(Maybe<&2, String>, ArP.init.err(c), None{}, AE.ev.err_none(c, name, cap)) : {ArP.init.check(_, old, c, False{}, harness, seg, runs, pend) == ArS.Refuse{ArP.t_same()} : ArS.Res}
      ikr.old(old, c, harness, seg, mode, runs, pend, kind)
