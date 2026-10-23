# eukhe: the proof of LAW run_abort_ends_now

import Base
import ../../bend/run.bend as Rn
import ../../laws/run.bend as Run
import ../base/bool/misc.bend as LBoolMisc

def abort_now(+cfg: Rn.Cfg, s: Rn.St, nd: {Rn.done(s) == False{} : Bool}) -> {Rn.St.ph(Rn.step(cfg, s, Rn.Abort{})) == Rn.Aborted{} : Rn.Ph}:
  match s:
    case Rn.St{ph, r, c, a, n, p}:
      match ph:
        case Rn.Prepare{}:
          {==}
        case Rn.Call{}:
          {==}
        case Rn.Compact{over}:
          {==}
        case Rn.Tools{}:
          {==}
        case Rn.Answered{}:
          LBoolMisc.absurd({Rn.St.ph(Rn.step(cfg, Rn.St{Rn.Answered{}, r, c, a, n, p}, Rn.Abort{})) == Rn.Aborted{} : Rn.Ph}, Equal.sym(Bool, True{}, False{}, nd))
        case Rn.Aborted{}:
          {==}
        case Rn.Failed{why}:
          LBoolMisc.absurd({Rn.St.ph(Rn.step(cfg, Rn.St{Rn.Failed{why}, r, c, a, n, p}, Rn.Abort{})) == Rn.Aborted{} : Rn.Ph}, Equal.sym(Bool, True{}, False{}, nd))

def Run.run_abort_ends_now(cfg, s, live):
  abort_now(cfg, s, live)
