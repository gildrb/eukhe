# eukhe: the proof of LAW run_defers_spend_the_polls
#
# PROOF: the poll invariant of run_polls_need_defers (PInv, by induction
# on the inputs) says it: in a call, the deferred replies in a row and
# the polls left make the cap.

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run
import ./run_polls_need_defers.bend as PP

# in a call, the deferred replies in a row and the polls left make the cap
def dp.of(+cfg: RnState.Cfg, +s: RnState.St, +k: Nat, i: PP.PInv(cfg, s, k)) -> Or({Run.in_call(RnState.St.ph(s)) == False{} : Bool}, {Nat.add(k, RnState.St.p(s)) == RnState.Cfg.polls(cfg) : Nat}):
  match cfg:
    case RnState.Cfg{cap, pp, aa, nn}:
      match s:
        case RnState.St{ph, r, c, a, n, p}:
          match ph:
            case RnState.Call{}:
              Inr{i}
            case RnState.Prepare{}:
              Inl{{==}}
            case RnState.Compact{over}:
              Inl{{==}}
            case RnState.Tools{}:
              Inl{{==}}
            case RnState.Answered{}:
              Inl{{==}}
            case RnState.Aborted{}:
              Inl{{==}}
            case RnState.Failed{why}:
              Inl{{==}}

def Run.run_defers_spend_the_polls(cfg, evs):
  dp.of(cfg, RnStep.run(cfg, evs), RnMeasure.defers(cfg, evs), PP.pinv_run(evs, cfg, RnState.init(cfg), 0n, Unit{}))
