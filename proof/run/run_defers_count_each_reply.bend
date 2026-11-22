# eukhe: the proof of LAW run_defers_count_each_reply
#
# PROOF: the fold behind RnMeasure.defers over evs ++ [e] is one step of it
# after the fold over evs (dd.app); that step, defers.at, is the spec's
# defers_after, by cases on the phase and the input.

import Base
import ../../bend/run/measure.bend as RnMeasure
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run

# the fold over evs then more goes on from the fold over evs
def dd.app(evs: List<&2, RnState.Ev>, -more: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +k: Nat) -> {RnMeasure.defers.go(more, cfg, RnStep.run.go(evs, cfg, s), RnMeasure.defers.go(evs, cfg, s, k)) == RnMeasure.defers.go(List.append(&2, RnState.Ev, evs, more), cfg, s, k) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      dd.app(rest, more, cfg, RnStep.step(cfg, s, e), RnMeasure.defers.at(RnState.St.ph(s), e, k))

# one input: the code's count is the spec's
def dd.c(ph: RnState.Ph, e: RnState.Ev, +k: Nat) -> {RnMeasure.defers.at(ph, e, k) == Run.defers_after(ph, e, k) : Nat}:
  match ph:
    case RnState.Call{}:
      match e:
        case RnState.Abort{}:
          {==}
        case RnState.Go{reply, fin, got}:
          match reply:
            case RnState.Deferred{}:
              {==}
            case RnState.Plain{}:
              {==}
            case RnState.Calls{}:
              {==}
            case RnState.Error{retryable, noted}:
              {==}
            case RnState.Overflow{cut}:
              {==}
    case RnState.Prepare{}:
      {==}
    case RnState.Compact{over}:
      {==}
    case RnState.Tools{}:
      {==}
    case RnState.Answered{}:
      {==}
    case RnState.Aborted{}:
      {==}
    case RnState.Failed{why}:
      {==}

# one more input, after any inputs
def dd.snoc(+cfg: RnState.Cfg, +evs: List<&2, RnState.Ev>, +e: RnState.Ev) -> {RnMeasure.defers(cfg, List.append(&2, RnState.Ev, evs, e <> Nil{})) == Run.defers_after(RnState.St.ph(RnStep.run(cfg, evs)), e, RnMeasure.defers(cfg, evs)) : Nat}:
  %dd.app(evs, e <> Nil{}, cfg, RnState.init(cfg), 0n) : {_ == Run.defers_after(RnState.St.ph(RnStep.run(cfg, evs)), e, RnMeasure.defers(cfg, evs)) : Nat}
  dd.c(RnState.St.ph(RnStep.run(cfg, evs)), e, RnMeasure.defers(cfg, evs))

def Run.run_defers_count_each_reply(cfg, evs, e):
  ({==}, dd.snoc(cfg, evs, e))
