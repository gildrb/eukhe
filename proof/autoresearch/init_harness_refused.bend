# eukhe: the proof of LAW init_harness_refused: the configuration has no
# error (AE.ev.err_none); a first init or a new segment then asks for the
# harness

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS
import ./base/events.bend as AE

def ihr.old(old: Maybe<&2, ArS.Cfg>, +c: ArS.Cfg, fresh: Bool, seg: Nat, -mode: ArS.Mode, runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, new: {Bool.or(ArM.ar_no_cfg(ArS.St{old, seg, mode, runs, pend}), fresh) == True{} : Bool}) -> {ArP.init.old(old, c, fresh, False{}, seg, runs, pend) == ArS.Refuse{ArP.t_harness()} : ArS.Res}:
  match old:
    case None{}:
      {==}
    case Some{o}:
      match fresh:
        case True{}:
          {==}
        case False{}:
          AS.as.absurd({ArP.init.old(Some{o}, c, False{}, False{}, seg, runs, pend) == ArS.Refuse{ArP.t_harness()} : ArS.Res}, new)

def AutoresearchEvents.init_harness_refused(s, c, fresh, name, cap, new):
  match s:
    case ArS.St{old, seg, mode, runs, pend}:
      %Equal.sym(Maybe<&2, String>, ArP.init.err(c), None{}, AE.ev.err_none(c, name, cap)) : {ArP.init.check(_, old, c, fresh, False{}, seg, runs, pend) == ArS.Refuse{ArP.t_harness()} : ArS.Res}
      ihr.old(old, c, fresh, seg, mode, runs, pend, new)
