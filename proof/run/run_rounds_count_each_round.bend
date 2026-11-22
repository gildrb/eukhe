# eukhe: the proof of LAW run_rounds_count_each_round
#
# PROOF: the fold behind RnMeasure.rounds over evs ++ [e] is one step of it
# after the fold over evs (rr.app); that step, `counted`, is the spec's
# one_more of counted_round, by cases on the phase and the input.

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run

# the fold over evs then more goes on from the fold over evs
def rr.app(evs: List<&2, RnState.Ev>, -more: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +k: Nat) -> {RnMeasure.rounds.go(more, cfg, RnStep.run.go(evs, cfg, s), RnMeasure.rounds.go(evs, cfg, s, k)) == RnMeasure.rounds.go(List.append(&2, RnState.Ev, evs, more), cfg, s, k) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      rr.app(rest, more, cfg, RnStep.step(cfg, s, e), RnMeasure.counted(RnState.St.ph(s), e, k))

# one input: the code's count is the spec's
def rr.c(ph: RnState.Ph, e: RnState.Ev, +k: Nat) -> {RnMeasure.counted(ph, e, k) == Run.one_more(Run.counted_round(ph, e), k) : Nat}:
  match ph:
    case RnState.Tools{}:
      match e:
        case RnState.Abort{}:
          {==}
        case RnState.Go{reply, fin, got}:
          match fin:
            case RnState.Goes{}:
              {==}
            case RnState.Stops{}:
              {==}
            case RnState.Resets{}:
              {==}
    case RnState.Prepare{}:
      {==}
    case RnState.Call{}:
      {==}
    case RnState.Compact{over}:
      {==}
    case RnState.Answered{}:
      {==}
    case RnState.Aborted{}:
      {==}
    case RnState.Failed{why}:
      {==}

# one more input, after any inputs
def rr.snoc(+cfg: RnState.Cfg, +evs: List<&2, RnState.Ev>, +e: RnState.Ev) -> {RnMeasure.rounds(cfg, List.append(&2, RnState.Ev, evs, e <> Nil{})) == Run.one_more(Run.counted_round(RnState.St.ph(RnStep.run(cfg, evs)), e), RnMeasure.rounds(cfg, evs)) : Nat}:
  %rr.app(evs, e <> Nil{}, cfg, RnState.init(cfg), 0n) : {_ == Run.one_more(Run.counted_round(RnState.St.ph(RnStep.run(cfg, evs)), e), RnMeasure.rounds(cfg, evs)) : Nat}
  rr.c(RnState.St.ph(RnStep.run(cfg, evs)), e, RnMeasure.rounds(cfg, evs))

def Run.run_rounds_count_each_round(cfg, evs, e):
  ({==}, rr.snoc(cfg, evs, e))
