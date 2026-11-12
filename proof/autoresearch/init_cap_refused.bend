# eukhe: the proof of LAW init_cap_refused: the name passes the code's
# test (AE.ev.name), and a cap of 0 fails its cap test

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/events.bend as AE

def icr.of(+c: ArS.Cfg, old: Maybe<&2, ArS.Cfg>, fresh: Bool, harness: Bool, seg: Nat, runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, name: {ArP.name_ok(ArS.Cfg.metric(c)) == True{} : Bool}, zero: {ArS.Cfg.max(c) == Some{0n} : Maybe<&2, Nat>}) -> {ArP.init.check(ArP.init.err(c), old, c, fresh, harness, seg, runs, pend) == ArS.Refuse{ArP.t_cap()} : ArS.Res}:
  %Equal.sym(Bool, ArP.name_ok(ArS.Cfg.metric(c)), True{}, name) : {ArP.init.check(ArP.init.err.name(_, ArS.Cfg.max(c)), old, c, fresh, harness, seg, runs, pend) == ArS.Refuse{ArP.t_cap()} : ArS.Res}
  %Equal.sym(Maybe<&2, Nat>, ArS.Cfg.max(c), Some{0n}, zero) : {ArP.init.check(ArP.init.err.max(ArP.cap_ok(_)), old, c, fresh, harness, seg, runs, pend) == ArS.Refuse{ArP.t_cap()} : ArS.Res}
  {==}

def AutoresearchEvents.init_cap_refused(s, c, fresh, harness, name, zero):
  match s:
    case ArS.St{old, seg, mode, runs, pend}:
      icr.of(c, old, fresh, harness, seg, runs, pend, AE.ev.name(ArS.Cfg.metric(c), True{}, name), zero)
