# eukhe: the proof of LAW init_name_refused: the law's name test is the
# code's (AE.ev.name), so the configuration's first error is the name's

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/events.bend as AE

def inr.of(+c: ArS.Cfg, old: Maybe<&2, ArS.Cfg>, fresh: Bool, harness: Bool, seg: Nat, runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, bad: {ArP.name_ok(ArS.Cfg.metric(c)) == False{} : Bool}) -> {ArP.init.check(ArP.init.err(c), old, c, fresh, harness, seg, runs, pend) == ArS.Refuse{ArP.t_name()} : ArS.Res}:
  %Equal.sym(Bool, ArP.name_ok(ArS.Cfg.metric(c)), False{}, bad) : {ArP.init.check(ArP.init.err.name(_, ArS.Cfg.max(c)), old, c, fresh, harness, seg, runs, pend) == ArS.Refuse{ArP.t_name()} : ArS.Res}
  {==}

def AutoresearchEvents.init_name_refused(s, c, fresh, harness, bad):
  match s:
    case ArS.St{old, seg, mode, runs, pend}:
      inr.of(c, old, fresh, harness, seg, runs, pend, AE.ev.name(ArS.Cfg.metric(c), False{}, bad))
