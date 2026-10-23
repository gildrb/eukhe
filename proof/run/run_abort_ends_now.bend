# eukhe: the proof of LAW run_abort_ends_now

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ../base/logic/logic.bend as LLogicLogic

def abort_now(+cfg: RnState.Cfg, s: RnState.St, nd: {RnState.done(s) == False{} : Bool}) -> {RnState.St.ph(RnStep.step(cfg, s, RnState.Abort{})) == RnState.Aborted{} : RnState.Ph}:
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      match ph:
        case RnState.Prepare{}:
          {==}
        case RnState.Call{}:
          {==}
        case RnState.Compact{over}:
          {==}
        case RnState.Tools{}:
          {==}
        case RnState.Answered{}:
          LLogicLogic.absurd({RnState.St.ph(RnStep.step(cfg, RnState.St{RnState.Answered{}, r, c, a, n, p}, RnState.Abort{})) == RnState.Aborted{} : RnState.Ph}, Equal.sym(Bool, True{}, False{}, nd))
        case RnState.Aborted{}:
          {==}
        case RnState.Failed{why}:
          LLogicLogic.absurd({RnState.St.ph(RnStep.step(cfg, RnState.St{RnState.Failed{why}, r, c, a, n, p}, RnState.Abort{})) == RnState.Aborted{} : RnState.Ph}, Equal.sym(Bool, True{}, False{}, nd))

def Run.run_abort_ends_now(cfg, s, live):
  abort_now(cfg, s, live)
